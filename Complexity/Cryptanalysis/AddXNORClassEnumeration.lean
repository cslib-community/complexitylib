/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORClasses
public import Complexity.Cryptanalysis.AddXNORSearch
public import Complexity.DataStructure.BinaryTrie.Buckets
import Mathlib.Algebra.BigOperators.Ring.List
import all Complexity.Cryptanalysis.AddXNORClasses
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Nodup

/-!
# Quarter-indexed low-bit class enumeration

[WangLvShenZhang2027], Lemma 8, PDF pp. 21–22. The first quarter's
full states are indexed by their low bits, retaining every operator witness in
each bucket. For each second-quarter word we compute its projected inverse from
the requested class, look up one bucket, and evaluate the full second quarter
only on hits. In particular this is not exhaustive half-enumeration followed by
a filter. Collisions retain all indexed witnesses.

`foldClass` sends hits directly to a consumer. `classRecords` is a mathematical
observer used to specify that fold; the streaming implementation does not build
it. Resource statements in this module count dictionary nodes, chain-step calls
and emitted records. They do not certify native instructions, binary decoding,
garbage collection or peak storage of a compiled program. The full native
Lemma 8 and Theorem 7 resource endpoints remain separate obligations.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR

open Cslib.DataStructure Cslib.DataStructure.BinaryTrie

namespace ClassEnumeration

/-- A first-quarter record retains its actual full state and indexed witness. -/
structure Prefix (m : ℕ) where
  /-- Full-width state after the first quarter. -/
  state : BitVec m
  /-- First-quarter operators in their original order. -/
  operators : List Bool
  deriving DecidableEq

/-- An emitted half record retains both quarters, including coincident states. -/
structure Record (m : ℕ) where
  /-- First-quarter operators. -/
  first : List Bool
  /-- Second-quarter operators. -/
  second : List Bool
  /-- Full state after both quarters. -/
  state : BitVec m
  deriving DecidableEq

/-- All first-quarter records; no full half list is constructed. -/
@[expose] def prefixes {m : ℕ} (as : List (BitVec m)) (s : BitVec m) : List (Prefix m) :=
  (operatorWords as.length).map fun bs => ⟨eval (bs.zip as) s, bs⟩

/-- First-quarter bucket key, constructed from the actual low state. -/
@[expose] def key {m : ℕ} (p : ℕ) (r : Prefix m) : List Bool :=
  stateKey (r.state.setWidth p)

/-- Build the quarter bucketIndex before scanning the second quarter. -/
@[expose] def prepare {m : ℕ} (p : ℕ) (as : List (BitVec m)) (s : BitVec m) :
    BinaryTrie (List (Prefix m)) := bucketIndex (key p) (prefixes as s)

/-- Project the actual second-quarter operands before evaluating inverses. -/
@[expose] def query {m p : ℕ} (as : List (BitVec m)) (bs : List Bool) (g : BitVec p) :
    List Bool := stateKey (backward (bs.zip (as.map (BitVec.setWidth p))) g)

/-- Compute a full-width output only for a bucket hit. -/
@[expose] def emit {m : ℕ} (as : List (BitVec m)) (bs : List Bool) (r : Prefix m) : Record m :=
  ⟨r.operators, bs, eval (bs.zip as) r.state⟩

/-- Mathematical output observer. Unlike `foldClass`, this collects every hit. -/
@[expose] def classRecords {m p : ℕ} (first second : List (BitVec m))
    (s : BitVec m) (g : BitVec p) : List (Record m) :=
  let t := prepare p first s
  (operatorWords second.length).flatMap fun bs =>
    (bucket t (query second bs g)).map (emit second bs)

/-- Stream a class to a consumer without materializing its full list. The
consumer controls retained output; choosing list insertion intentionally collects
the class, while a dictionary-lookup consumer need not retain any output. -/
@[expose] def foldClass {m p : ℕ} {α : Type*} (consume : α → Record m → α)
    (first second : List (BitVec m)) (s : BitVec m) (g : BitVec p) (initial : α) : α :=
  let t := prepare p first s
  (operatorWords second.length).foldl (fun acc bs =>
    (bucket t (query second bs g)).foldl
      (fun acc r => consume acc (emit second bs r)) acc) initial

/-- Every consumer sees exactly the specified record sequence, with its original
order and multiplicity. This statement is independent of the consumer's memory. -/
theorem foldClass_eq {m p : ℕ} {α : Type*} (consume : α → Record m → α)
    (first second : List (BitVec m)) (s : BitVec m) (g : BitVec p) (initial : α) :
    foldClass consume first second s g initial =
      (classRecords first second s g).foldl consume initial := by
  simp [foldClass, classRecords, List.foldl_flatMap, List.foldl_map]

private theorem zip_project {m : ℕ} (p : ℕ) (bs : List Bool) (as : List (BitVec m)) :
    bs.zip (as.map (BitVec.setWidth p)) = project p (bs.zip as) := by
  induction bs generalizing as with
  | nil => rfl
  | cons b bs ih =>
    cases as with
    | nil => rfl
    | cons a as => simp [project, ih]

/-- The bucket test is precisely the class condition, not a heuristic filter. -/
theorem bucket_test {m p : ℕ} (hp : p ≤ m) (as : List (BitVec m))
    (bs : List Bool) (r : Prefix m) (g : BitVec p) :
    key p r = query as bs g ↔ (emit as bs r).state.setWidth p = g := by
  rw [key, query, stateKey_injective p |>.eq_iff]
  rw [zip_project, emit]
  have h := eval_append_eq_iff ([] : List (Bool × BitVec p))
    (project p (bs.zip as)) (r.state.setWidth p) g
  simpa only [List.nil_append, eval, eval_project hp, backward_project hp] using h.symm

private theorem mem_prefixes {m : ℕ} (as : List (BitVec m)) (s : BitVec m) (r : Prefix m) :
    r ∈ prefixes as s ↔ r.operators.length = as.length ∧
      r.state = eval (r.operators.zip as) s := by
  simp only [prefixes, List.mem_map, mem_operatorWords]
  constructor
  · rintro ⟨bs, hb, hr⟩
    subst r
    exact ⟨hb, rfl⟩
  · rintro ⟨hl, he⟩
    exact ⟨r.operators, hl, by cases r; simp_all⟩

/-- Exact completeness and soundness for every indexed pair of quarter words.
Repeated states remain separate records, with no distinct-operand assumption. -/
theorem mem_classRecords {m p : ℕ} (hp : p ≤ m)
    (first second : List (BitVec m)) (s : BitVec m) (g : BitVec p) (r : Record m) :
    r ∈ classRecords first second s g ↔
      r.first.length = first.length ∧ r.second.length = second.length ∧
      r.state = eval (r.second.zip second) (eval (r.first.zip first) s) ∧
      r.state.setWidth p = g := by
  simp only [classRecords, List.mem_flatMap, mem_operatorWords, List.mem_map,
    prepare, bucket_bucketIndex, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨bs, hb, pre, ⟨hpre, hkey⟩, hr⟩
    have ht := (bucket_test hp second bs pre g).1 hkey
    obtain ⟨hlen, hstate⟩ := (mem_prefixes first s pre).1 hpre
    subst r
    exact ⟨hlen, hb, by simp [emit, hstate], ht⟩
  · rintro ⟨hfirst, hsecond, hstate, hlow⟩
    let pre : Prefix m := ⟨eval (r.first.zip first) s, r.first⟩
    have he : emit second r.second pre = r := by
      cases r
      simp_all [emit, pre]
    refine ⟨r.second, hsecond, pre, ⟨?_, ?_⟩, he⟩
    · exact (mem_prefixes first s pre).2 ⟨hfirst, rfl⟩
    · apply (bucket_test hp second r.second pre g).2
      rw [he]
      exact hlow

/-- Every indexed quarter pair occurs at most once, even with collisions. -/
theorem operatorWords_nodup (n : ℕ) : (operatorWords n).Nodup := by
  induction n with
  | zero => simp [operatorWords]
  | succ n ih =>
    rw [operatorWords, List.nodup_append]
    refine ⟨ih.map (by intros a b h; exact List.cons.inj h |>.2),
      ih.map (by intros a b h; exact List.cons.inj h |>.2), ?_⟩
    simp

/-- First-quarter witnesses are distinct even when their states coincide. -/
theorem prefixes_nodup {m : ℕ} (as : List (BitVec m)) (s : BitVec m) :
    (prefixes as s).Nodup :=
  (operatorWords_nodup as.length).map (by
    intro a b h
    exact congrArg Prefix.operators h)

/-- Exact number of first-quarter records prepared. -/
theorem prefixes_length {m : ℕ} (as : List (BitVec m)) (s : BitVec m) :
    (prefixes as s).length = 2 ^ as.length := by
  simp [prefixes, operatorWords_length]

/-- Quarter preparation has at most `(p+1)2^a` retained dictionary nodes,
independently of the size of the requested half class. -/
theorem prepare_nodes_le {m : ℕ} (p : ℕ) (as : List (BitVec m)) (s : BitVec m) :
    (prepare p as s).nodes ≤ 2 ^ as.length * (p + 1) := by
  simpa only [prepare, prefixes_length] using
    bucketIndex_nodes_le (key p) (prefixes as s) p (by intro r _; simp [key, stateKey])

/-- Number of actual projected inverse chain steps while visiting the second
quarter. Evaluating a full half on every second-quarter word is avoided. -/
@[expose] def queryStepCalls {m : ℕ} (second : List (BitVec m)) : ℕ :=
  enumerationStepCalls second

/-- Number of full-width steps on hits. Every hit executes the second quarter,
including when many witnesses reach the same full state. -/
@[expose] def hitStepCalls {m p : ℕ} (first second : List (BitVec m))
    (s : BitVec m) (g : BitVec p) : ℕ :=
  ((operatorWords second.length).map fun bs =>
    ((bucket (prepare p first s) (query second bs g)).map fun _ =>
      evalStepCalls (bs.zip second)).sum).sum

/-- Full-width step work is output-sensitive, with no class-balance premise. -/
theorem hitStepCalls_eq {m p : ℕ} (first second : List (BitVec m))
    (s : BitVec m) (g : BitVec p) :
    hitStepCalls first second s g = second.length * (classRecords first second s g).length := by
  unfold hitStepCalls classRecords
  rw [List.length_flatMap]
  simp only [List.length_map]
  rw [← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro bs hb
  have hlen := (mem_operatorWords bs second.length).1 hb
  simp [evalStepCalls_eq_length, List.length_zip, hlen, Nat.mul_comm]

/-- All counted chain evaluations in the quarter-based enumerator, including
first-quarter setup, projected inverse queries and full-width output recovery. -/
@[expose] def chainStepCalls {m p : ℕ} (first second : List (BitVec m))
    (s : BitVec m) (g : BitVec p) : ℕ :=
  enumerationStepCalls first + queryStepCalls second + hitStepCalls first second s g

/-- Lemma 8's output-sensitive chain-call count. This is a derived count of
executed evaluations, not a native runtime assigned to a pure function. -/
theorem chainStepCalls_eq {m p : ℕ} (first second : List (BitVec m))
    (s : BitVec m) (g : BitVec p) :
    chainStepCalls first second s g = first.length * 2 ^ first.length +
      second.length * 2 ^ second.length +
      second.length * (classRecords first second s g).length := by
  simp [chainStepCalls, queryStepCalls, enumerationStepCalls_eq, hitStepCalls_eq]

/-- The streaming observer never repeats an indexed pair. -/
theorem classRecords_nodup {m p : ℕ} (first second : List (BitVec m))
    (s : BitVec m) (g : BitVec p) : (classRecords first second s g).Nodup := by
  apply List.nodup_flatMap.2
  constructor
  · intro bs _
    apply List.Nodup.map_on ?_ (bucket_bucketIndex_nodup (key p) (prefixes first s)
      (prefixes_nodup first s) (query second bs g))
    intro a ha b hb he
    have hfirst := congrArg Record.first he
    change a.operators = b.operators at hfirst
    have ha' := (List.mem_filter.1 (bucket_bucketIndex (key p) (prefixes first s)
      (query second bs g) ▸ ha)).1
    have hb' := (List.mem_filter.1 (bucket_bucketIndex (key p) (prefixes first s)
      (query second bs g) ▸ hb)).1
    have hsa := (mem_prefixes first s a).1 ha'
    have hsb := (mem_prefixes first s b).1 hb'
    cases a; cases b
    simp_all
  · apply (operatorWords_nodup second.length).imp
    intro a b hab r ha hb
    obtain ⟨x, _, hx⟩ := List.mem_map.1 ha
    obtain ⟨y, _, hy⟩ := List.mem_map.1 hb
    exact hab (by simpa only [emit] using congrArg Record.second (hx.trans hy.symm))

private theorem filter_length_eq_sum {α : Type*} (f : α → Bool) (xs : List α) :
    (xs.filter f).length = (xs.map fun a => if f a then 1 else 0).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : f x <;> simp [h, ih, Nat.add_comm]

/-- Cardinality is computed by the same low-bit predicate as the counter DP. -/
theorem classRecords_length {m p : ℕ} (hp : p ≤ m)
    (first second : List (BitVec m)) (s : BitVec m) (g : BitVec p) :
    (classRecords first second s g).length =
      ((operatorWords second.length).map fun ys =>
        ((operatorWords first.length).map fun xs =>
          if (eval (ys.zip second) (eval (xs.zip first) s)).setWidth p = g
          then 1 else 0).sum).sum := by
  simp only [classRecords, List.length_flatMap, List.length_map, prepare,
    bucket_bucketIndex, filter_length_eq_sum, prefixes, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro ys _
  congr 1
  apply List.map_congr_left
  intro xs _
  simp only [beq_iff_eq, bucket_test hp, emit]

private theorem append_bijective (a b : ℕ) :
    Function.Bijective (fun v : (Fin a → Bool) × (Fin b → Bool) => Fin.append v.1 v.2) := by
  constructor
  · intro ⟨x, y⟩ ⟨z, w⟩ h
    apply Prod.ext
    · funext i
      simpa using congrFun h (i.castAdd b)
    · funext i
      simpa using congrFun h (i.natAdd a)
  · intro f
    exact ⟨(fun i => f (i.castAdd b), fun i => f (i.natAdd a)), Fin.append_castAdd_natAdd⟩

private theorem steps_append {m a b : ℕ} (xs : Fin a → Bool) (ys : Fin b → Bool)
    (first : Fin a → BitVec m) (second : Fin b → BitVec m) :
    steps (Fin.append xs ys) (Fin.append first second) = steps xs first ++ steps ys second := by
  rw [← WordTable.steps_zip, List.ofFn_fin_append, List.ofFn_fin_append,
    List.zip_append (by simp), WordTable.steps_zip, WordTable.steps_zip]

/-- The exact emitted count equals the previously proved forward class count,
so counter preprocessing can select a side without enumerating the class. -/
theorem classRecords_length_eq_count {m p a b : ℕ} (hp : p ≤ m)
    (first : Fin a → BitVec m) (second : Fin b → BitVec m)
    (s : BitVec m) (g : BitVec p) :
    (classRecords (List.ofFn first) (List.ofFn second) s g).length =
      forwardClassCount p (Fin.append first second) s g := by
  rw [classRecords_length hp]
  simp only [List.length_ofFn, WordTable.sum_operatorWords, WordTable.steps_zip]
  unfold forwardClassCount
  rw [← Fintype.sum_bijective _ (append_bijective a b)
    (fun v => if (eval (steps (Fin.append v.1 v.2) (Fin.append first second)) s).setWidth p = g
      then 1 else 0)
    (fun bs => if (eval (steps bs (Fin.append first second)) s).setWidth p = g then 1 else 0)
    (fun _ => rfl), Fintype.sum_prod_type, Finset.sum_comm]
  simp only [steps_append, eval_append]

/-- Summing emitted records across all classes recovers every half witness,
with multiplicity. Per-class dependencies do not enter this identity. -/
theorem sum_classRecords_length {m p a b : ℕ} (hp : p ≤ m)
    (first : Fin a → BitVec m) (second : Fin b → BitVec m) (s : BitVec m) :
    ∑ g : BitVec p, (classRecords (List.ofFn first) (List.ofFn second) s g).length =
      2 ^ (a + b) := by
  simp only [classRecords_length_eq_count hp]
  exact sum_forwardClassCount p (Fin.append first second) s

/-- Inverse quarters undo the final block first. -/
theorem backward_append {m : ℕ} (xs ys : List (Bool × BitVec m)) (t : BitVec m) :
    backward (xs ++ ys) t = backward xs (backward ys t) := by
  apply (eval_bijective (xs ++ ys)).1
  rw [eval_backward, eval_append, eval_backward, eval_backward]

/-- Final-quarter records, retaining the original operator order. -/
@[expose] def backPrefixes {m : ℕ} (as : List (BitVec m)) (t : BitVec m) : List (Prefix m) :=
  (operatorWords as.length).map fun bs => ⟨backward (bs.zip as) t, bs⟩

/-- Index the final quarter by the low bits of its full backward state. -/
@[expose] def prepareBack {m : ℕ} (p : ℕ) (as : List (BitVec m)) (t : BitVec m) :
    BinaryTrie (List (Prefix m)) := bucketIndex (key p) (backPrefixes as t)

/-- The earlier inverse quarter queries a projected *forward* state. -/
@[expose] def queryBack {m p : ℕ} (as : List (BitVec m)) (bs : List Bool) (g : BitVec p) :
    List Bool := stateKey (eval (bs.zip (as.map (BitVec.setWidth p))) g)

/-- Recover a full backward state only on a bucket hit. -/
@[expose] def emitBack {m : ℕ} (as : List (BitVec m)) (bs : List Bool) (r : Prefix m) : Record m :=
  ⟨bs, r.operators, backward (bs.zip as) r.state⟩

/-- Mathematical observer for backward class enumeration. -/
@[expose] def backClassRecords {m p : ℕ} (first second : List (BitVec m))
    (t : BitVec m) (g : BitVec p) : List (Record m) :=
  let idx := prepareBack p second t
  (operatorWords first.length).flatMap fun bs =>
    (bucket idx (queryBack first bs g)).map (emitBack first bs)

/-- Backward streaming uses the same bucket traversal, with direction exchanged.
No full backward class is materialized unless the consumer collects it. -/
@[expose] def foldBackClass {m p : ℕ} {α : Type*} (consume : α → Record m → α)
    (first second : List (BitVec m)) (t : BitVec m) (g : BitVec p) (initial : α) : α :=
  let idx := prepareBack p second t
  (operatorWords first.length).foldl (fun acc bs =>
    (bucket idx (queryBack first bs g)).foldl
      (fun acc r => consume acc (emitBack first bs r)) acc) initial

/-- Every backward consumer sees precisely the observer sequence. -/
theorem foldBackClass_eq {m p : ℕ} {α : Type*} (consume : α → Record m → α)
    (first second : List (BitVec m)) (t : BitVec m) (g : BitVec p) (initial : α) :
    foldBackClass consume first second t g initial =
      (backClassRecords first second t g).foldl consume initial := by
  simp [foldBackClass, backClassRecords, List.foldl_flatMap, List.foldl_map]

private theorem back_bucket_test {m p : ℕ} (hp : p ≤ m) (as : List (BitVec m))
    (bs : List Bool) (r : Prefix m) (g : BitVec p) :
    key p r = queryBack as bs g ↔ (emitBack as bs r).state.setWidth p = g := by
  rw [key, queryBack, stateKey_injective p |>.eq_iff, zip_project]
  change r.state.setWidth p = eval (project p (bs.zip as)) g ↔
    (backward (bs.zip as) r.state).setWidth p = g
  rw [backward_project hp]
  constructor
  · intro h; rw [h, backward_eval]
  · intro h; rw [← h, eval_backward]

private theorem mem_backPrefixes {m : ℕ} (as : List (BitVec m)) (t : BitVec m) (r : Prefix m) :
    r ∈ backPrefixes as t ↔ r.operators.length = as.length ∧
      r.state = backward (r.operators.zip as) t := by
  simp only [backPrefixes, List.mem_map, mem_operatorWords]
  constructor
  · rintro ⟨bs, hb, hr⟩
    subst r
    exact ⟨hb, rfl⟩
  · rintro ⟨hl, he⟩
    exact ⟨r.operators, hl, by cases r; simp_all⟩

/-- Exact backward class semantics, including empty quarters and zero width. -/
theorem mem_backClassRecords {m p : ℕ} (hp : p ≤ m)
    (first second : List (BitVec m)) (t : BitVec m) (g : BitVec p) (r : Record m) :
    r ∈ backClassRecords first second t g ↔
      r.first.length = first.length ∧ r.second.length = second.length ∧
      r.state = backward (r.first.zip first) (backward (r.second.zip second) t) ∧
      r.state.setWidth p = g := by
  simp only [backClassRecords, List.mem_flatMap, mem_operatorWords, List.mem_map,
    prepareBack, bucket_bucketIndex, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨bs, hb, pre, ⟨hpre, hkey⟩, hr⟩
    have ht := (back_bucket_test hp first bs pre g).1 hkey
    obtain ⟨hlen, hstate⟩ := (mem_backPrefixes second t pre).1 hpre
    subst r
    exact ⟨hb, hlen, by simp [emitBack, hstate], ht⟩
  · rintro ⟨hfirst, hsecond, hstate, hlow⟩
    let pre : Prefix m := ⟨backward (r.second.zip second) t, r.second⟩
    have he : emitBack first r.first pre = r := by
      cases r
      simp_all [emitBack, pre]
    refine ⟨r.first, hfirst, pre, ⟨?_, ?_⟩, he⟩
    · exact (mem_backPrefixes second t pre).2 ⟨hsecond, rfl⟩
    · apply (back_bucket_test hp first r.first pre g).2
      rw [he]
      exact hlow

/-- Exact backward multiplicity as a sum over both indexed quarter words. -/
theorem backClassRecords_length {m p : ℕ} (hp : p ≤ m)
    (first second : List (BitVec m)) (t : BitVec m) (g : BitVec p) :
    (backClassRecords first second t g).length =
      ((operatorWords first.length).map fun xs => ((operatorWords second.length).map fun ys =>
        if (backward (xs.zip first) (backward (ys.zip second) t)).setWidth p = g
        then 1 else 0).sum).sum := by
  simp only [backClassRecords, List.length_flatMap, List.length_map, prepareBack,
    bucket_bucketIndex, filter_length_eq_sum, backPrefixes, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro xs _
  congr 1
  apply List.map_congr_left
  intro ys _
  simp only [beq_iff_eq, back_bucket_test hp, emitBack]

/-- Exact backward cardinality agrees with inverse counter preprocessing. -/
theorem backClassRecords_length_eq_count {m p a b : ℕ} (hp : p ≤ m)
    (first : Fin a → BitVec m) (second : Fin b → BitVec m)
    (t : BitVec m) (g : BitVec p) :
    (backClassRecords (List.ofFn first) (List.ofFn second) t g).length =
      backwardClassCount p (Fin.append first second) t g := by
  rw [backClassRecords_length hp, List.length_ofFn, List.length_ofFn]
  simp only [WordTable.sum_operatorWords, WordTable.steps_zip]
  unfold backwardClassCount
  rw [← Fintype.sum_bijective _ (append_bijective a b)
    (fun v => if (backward (steps (Fin.append v.1 v.2) (Fin.append first second)) t).setWidth p = g
      then 1 else 0)
    (fun bs => if (backward (steps bs (Fin.append first second)) t).setWidth p = g then 1 else 0)
    (fun _ => rfl), Fintype.sum_prod_type]
  simp only [steps_append, backward_append]

/-- Backward output across every class is exactly the whole suffix space. -/
theorem sum_backClassRecords_length {m p a b : ℕ} (hp : p ≤ m)
    (first : Fin a → BitVec m) (second : Fin b → BitVec m) (t : BitVec m) :
    ∑ g : BitVec p, (backClassRecords (List.ofFn first) (List.ofFn second) t g).length =
      2 ^ (a + b) := by
  simp only [backClassRecords_length_eq_count hp]
  exact sum_backwardClassCount p (Fin.append first second) t

/-- Retained nodes for the final-quarter bucketIndex obey the same quarter bound. -/
theorem prepareBack_nodes_le {m : ℕ} (p : ℕ) (as : List (BitVec m)) (t : BitVec m) :
    (prepareBack p as t).nodes ≤ 2 ^ as.length * (p + 1) := by
  simpa only [prepareBack, backPrefixes, List.length_map, operatorWords_length] using
    bucketIndex_nodes_le (key p) (backPrefixes as t) p (by intro r _; simp [key, stateKey])

/-- Actual full-width inverse steps performed on backward hits. -/
@[expose] def backHitStepCalls {m p : ℕ} (first second : List (BitVec m))
    (t : BitVec m) (g : BitVec p) : ℕ :=
  ((operatorWords first.length).map fun bs =>
    ((bucket (prepareBack p second t) (queryBack first bs g)).map fun _ =>
      evalStepCalls (bs.zip first)).sum).sum

/-- Backward recovery is output-sensitive, including repeated full states. -/
theorem backHitStepCalls_eq {m p : ℕ} (first second : List (BitVec m))
    (t : BitVec m) (g : BitVec p) :
    backHitStepCalls first second t g =
      first.length * (backClassRecords first second t g).length := by
  unfold backHitStepCalls backClassRecords
  rw [List.length_flatMap]
  simp only [List.length_map]
  rw [← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro bs hb
  have hlen := (mem_operatorWords bs first.length).1 hb
  simp [evalStepCalls_eq_length, List.length_zip, hlen, Nat.mul_comm]

/-- All backward chain calls, including projected queries and quarter setup. -/
@[expose] def backChainStepCalls {m p : ℕ} (first second : List (BitVec m))
    (t : BitVec m) (g : BitVec p) : ℕ :=
  enumerationStepCalls second + queryStepCalls first + backHitStepCalls first second t g

/-- Direction reversal exchanges the queried and indexed quarters. -/
theorem backChainStepCalls_eq {m p : ℕ} (first second : List (BitVec m))
    (t : BitVec m) (g : BitVec p) :
    backChainStepCalls first second t g = second.length * 2 ^ second.length +
      first.length * 2 ^ first.length +
      first.length * (backClassRecords first second t g).length := by
  simp [backChainStepCalls, queryStepCalls, enumerationStepCalls_eq, backHitStepCalls_eq]

/-- A backward class never repeats an indexed pair. -/
theorem backClassRecords_nodup {m p : ℕ} (first second : List (BitVec m))
    (t : BitVec m) (g : BitVec p) : (backClassRecords first second t g).Nodup := by
  apply List.nodup_flatMap.2
  constructor
  · intro bs _
    have hn : (backPrefixes second t).Nodup :=
      (operatorWords_nodup second.length).map (by
        intro a b h
        exact congrArg Prefix.operators h)
    apply List.Nodup.map_on ?_ (bucket_bucketIndex_nodup (key p) (backPrefixes second t)
      hn (queryBack first bs g))
    intro a ha b hb he
    have hsecond := congrArg Record.second he
    change a.operators = b.operators at hsecond
    have ha' := (List.mem_filter.1 (bucket_bucketIndex (key p) (backPrefixes second t)
      (queryBack first bs g) ▸ ha)).1
    have hb' := (List.mem_filter.1 (bucket_bucketIndex (key p) (backPrefixes second t)
      (queryBack first bs g) ▸ hb)).1
    have hsa := (mem_backPrefixes second t a).1 ha'
    have hsb := (mem_backPrefixes second t b).1 hb'
    cases a; cases b
    simp_all
  · apply (operatorWords_nodup first.length).imp
    intro a b hab r ha hb
    obtain ⟨x, _, hx⟩ := List.mem_map.1 ha
    obtain ⟨y, _, hy⟩ := List.mem_map.1 hb
    exact hab (by simpa only [emitBack] using congrArg Record.first (hx.trans hy.symm))

end ClassEnumeration

end Cslib.Cryptanalysis.AddXNOR
