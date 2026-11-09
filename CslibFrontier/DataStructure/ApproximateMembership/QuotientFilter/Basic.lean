/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.ApproximateMembership.Spec
public import CslibFrontier.DataStructure.Dictionary.WordRAM.LinearProbing.FiveWise
public import Mathlib.Data.Multiset.Sort

/-!
# Canonical Quotient Filter Model and Cluster Invariants

This file develops the pure combinatorial model of a canonical quotient filter
([Pagh, Pagh and Rao][PaghPaghRao2005]; [Bender et al.][BenderEtAl2012]) over a table of `2 ^ b`
slots storing `f`-bit remainders `Fin (2 ^ f)` with three metadata bits per slot (`isFull`,
`isOcc`, `isRunStart`).

## Design

1. **Canonical bucket runs (`bucketRun`, `taggedRun`):**
   For a finite set `S : Finset (Fin U)` of currently present keys, quotient map
   `quot : Fin U → Fin (2 ^ b)`, and remainder map `rem : Fin U → Fin (2 ^ f)`, each bucket
   `q : Fin (2 ^ b)` has a canonical sorted remainder list
   `bucketRun S quot rem q : List (Fin (2 ^ f))` obtained by sorting the multiset of remainders of
   keys in `S` with quotient `q`. Tagging the head of a non-empty bucket run with `true`
   (`isRunStart = true`) and continuation elements with `false` (`taggedRun`) makes run boundaries
   uniquely recoverable from the concatenated slot stream.

2. **Maximal full clusters and `IntervalValid` (`FilterInv`):**
   Every maximal contiguous full interval `[o .. o + ℓ)` (preceded by an empty slot at
   `backSlot b o 1` and followed by an empty slot at `probeSlot b o ℓ`) holds the exact
   concatenation
   `(List.range ℓ).flatMap (fun j => taggedRun (bucketRun S quot rem (probeSlot b o j)))`,
   with every prefix `m < ℓ` satisfying `m + 1 ≤ ∑ j ≤ m, |bucketRun ... (probeSlot b o j)|`.
   Consequently:
   - Slot occupancy and slot contents depend **only** on the current key set `S` and hash pair
     `(quot, rem)` (history-independent canonical runs).
   - The number of keys of `S` whose quotient falls into a maximal full cluster
     `cyclicInterval b (quot u) a ℓ` equals `ℓ` (`card_filter_quot_mem_cyclicInterval_eq`),
     transferring the $5$-wise independent dyadic scale-overload bound directly to quotient-filter
     clusters (`clusterLen_sub_one_le_sum_scaleOverload`).
   - Run boundaries inside any cluster `[o .. o + ℓ)` are characterized by the monotone counting
     equivalence `i < runOffset S quot rem o m ↔ runsBefore st o (i + 1) ≤ occBefore st o m`
     (`lt_runOffset_iff`).

## Main definitions

* `Cslib.DataStructure.ApproximateMembership.QuotientFilter.bucketRun`,
  `Cslib.DataStructure.ApproximateMembership.QuotientFilter.taggedRun`: canonical sorted bucket
  runs and run-start tagged runs.
* `Cslib.DataStructure.ApproximateMembership.QuotientFilter.FilterState`,
  `Cslib.DataStructure.ApproximateMembership.QuotientFilter.IntervalValid`,
  `Cslib.DataStructure.ApproximateMembership.QuotientFilter.FilterInv`: pure slot-table state and
  canonical cluster invariant.
* `FilterInv.backLen`, `FilterInv.fwdLen`, `FilterInv.clusterLen`: backward, forward, and total
  full-cluster lengths around a bucket.
* `FilterInv.querySlot`: pure membership query on a canonical quotient filter.

## Main results

* `IntervalValid.lt_runOffset_iff`: exact run-offset characterization via prefix counts of
  `isRunStart` and `isOcc`.
* `FilterInv.card_filter_quot_mem_cyclicInterval_eq`: a maximal full cluster of length `ℓ` around
  `q` contains the quotients of `ℓ` keys of `S`.
* `FilterInv.clusterLen_sub_one_le_sum_scaleOverload`: pointwise bound of
  `clusterLen st (quot u) - 1` by the dyadic scale-overload sum for `S.erase u`.
* `FilterInv.querySlot_eq_true_iff`: exact fingerprint-collision characterization of `querySlot`.

## References

* [A. Pagh, R. Pagh and S. S. Rao, *An optimal Bloom filter replacement*][PaghPaghRao2005]
* [M. A. Bender, M. Farach-Colton, R. Johnson, R. Kraner, B. C. Kuszmaul, D. Medjedovic, P. Montes,
  P. Shetty, R. P. Spillane and E. Zadok, *Don't thrash: how to cache your hash on
  flash*][BenderEtAl2012]
-/

public section

namespace Cslib.DataStructure.ApproximateMembership.QuotientFilter

open Finset
open Cslib.DataStructure.Dictionary.WordRAM.LinearProbing

/-! ## Section 1: Canonical sorted bucket runs and tagged runs -/

/-- Canonical sorted list of `f`-bit remainders of keys in `S` whose quotient is `q`. -/
@[expose] noncomputable def bucketRun {U b f : ℕ} (S : Finset (Fin U))
    (quot : Fin U → Fin (2 ^ b)) (rem : Fin U → Fin (2 ^ f)) (q : Fin (2 ^ b)) :
    List (Fin (2 ^ f)) :=
  ((S.filter fun x => quot x = q).val.map rem).sort (· ≤ ·)

@[simp]
theorem bucketRun_empty {U b f : ℕ} (quot : Fin U → Fin (2 ^ b)) (rem : Fin U → Fin (2 ^ f))
    (q : Fin (2 ^ b)) :
    bucketRun (∅ : Finset (Fin U)) quot rem q = [] := by
  simp [bucketRun]

theorem length_bucketRun {U b f : ℕ} (S : Finset (Fin U))
    (quot : Fin U → Fin (2 ^ b)) (rem : Fin U → Fin (2 ^ f)) (q : Fin (2 ^ b)) :
    (bucketRun S quot rem q).length = #(S.filter fun x => quot x = q) := by
  simp [bucketRun, Finset.card_def]

theorem bucketRun_eq_nil_iff {U b f : ℕ} (S : Finset (Fin U))
    (quot : Fin U → Fin (2 ^ b)) (rem : Fin U → Fin (2 ^ f)) (q : Fin (2 ^ b)) :
    bucketRun S quot rem q = [] ↔ ∀ x ∈ S, quot x ≠ q := by
  rw [← List.length_eq_zero_iff, length_bucketRun, Finset.card_eq_zero, Finset.filter_eq_empty_iff]

theorem mem_bucketRun_iff {U b f : ℕ} (S : Finset (Fin U))
    (quot : Fin U → Fin (2 ^ b)) (rem : Fin U → Fin (2 ^ f)) (q : Fin (2 ^ b))
    (r : Fin (2 ^ f)) :
    r ∈ bucketRun S quot rem q ↔ ∃ x ∈ S, quot x = q ∧ rem x = r := by
  simp only [bucketRun, Multiset.mem_sort, Multiset.mem_map, Finset.mem_val, Finset.mem_filter]
  tauto

theorem pairwise_le_bucketRun {U b f : ℕ} (S : Finset (Fin U))
    (quot : Fin U → Fin (2 ^ b)) (rem : Fin U → Fin (2 ^ f)) (q : Fin (2 ^ b)) :
    (bucketRun S quot rem q).Pairwise (· ≤ ·) :=
  Multiset.pairwise_sort _ _

theorem bucketRun_insert_of_ne {U b f : ℕ} (S : Finset (Fin U))
    (quot : Fin U → Fin (2 ^ b)) (rem : Fin U → Fin (2 ^ f)) (u : Fin U)
    {q : Fin (2 ^ b)} (hne : quot u ≠ q) :
    bucketRun (insert u S) quot rem q = bucketRun S quot rem q := by
  dsimp only [bucketRun]
  rw [Finset.filter_insert, ite_eq_right_iff.mpr fun h => absurd h hne]

theorem bucketRun_insert_self {U b f : ℕ} {S : Finset (Fin U)}
    (quot : Fin U → Fin (2 ^ b)) (rem : Fin U → Fin (2 ^ f)) {u : Fin U} (hu : u ∉ S) :
    bucketRun (insert u S) quot rem (quot u) =
      List.orderedInsert (· ≤ ·) (rem u) (bucketRun S quot rem (quot u)) := by
  refine List.Perm.eq_of_pairwise'
    (pairwise_le_bucketRun (insert u S) quot rem (quot u))
    ((pairwise_le_bucketRun S quot rem (quot u)).orderedInsert _ _) ?_
  have hfilter : (insert u S).filter (fun x => quot x = quot u) =
      insert u (S.filter fun x => quot x = quot u) := by
    rw [Finset.filter_insert, ite_eq_left_iff.mpr fun h => absurd rfl h]
  have hu_notMem : u ∉ S.filter (fun x => quot x = quot u) := by
    simp [hu]
  have hval : ((insert u S).filter (fun x => quot x = quot u)).val.map rem =
      rem u ::ₘ ((S.filter (fun x => quot x = quot u)).val.map rem) := by
    rw [hfilter, Finset.insert_val_of_notMem hu_notMem, Multiset.map_cons]
  rw [← Multiset.coe_eq_coe]
  have h1 : (bucketRun (insert u S) quot rem (quot u) : Multiset (Fin (2 ^ f))) =
      rem u ::ₘ ((S.filter (fun x => quot x = quot u)).val.map rem) := by
    dsimp only [bucketRun]
    rw [Multiset.sort_eq, hval]
  have h2 : (List.orderedInsert (· ≤ ·) (rem u) (bucketRun S quot rem (quot u)) :
      Multiset (Fin (2 ^ f))) =
      rem u ::ₘ ((S.filter (fun x => quot x = quot u)).val.map rem) := by
    have hp := List.perm_orderedInsert (· ≤ ·) (rem u) (bucketRun S quot rem (quot u))
    have hcoe := Multiset.coe_eq_coe.mpr hp
    rw [hcoe, ← Multiset.cons_coe]
    dsimp only [bucketRun]
    rw [Multiset.sort_eq]
  exact h1.trans h2.symm

theorem bucketRun_erase_of_ne {U b f : ℕ} (S : Finset (Fin U))
    (quot : Fin U → Fin (2 ^ b)) (rem : Fin U → Fin (2 ^ f)) (u : Fin U)
    {q : Fin (2 ^ b)} (hne : quot u ≠ q) :
    bucketRun (S.erase u) quot rem q = bucketRun S quot rem q := by
  dsimp only [bucketRun]
  have hfilter : (S.erase u).filter (fun x => quot x = q) = S.filter (fun x => quot x = q) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨_, hx⟩, hq⟩
      exact ⟨hx, hq⟩
    · rintro ⟨hx, hq⟩
      refine ⟨⟨?_, hx⟩, hq⟩
      rintro rfl
      exact hne hq
  rw [hfilter]

theorem bucketRun_erase_self {U b f : ℕ} {S : Finset (Fin U)}
    (quot : Fin U → Fin (2 ^ b)) (rem : Fin U → Fin (2 ^ f)) {u : Fin U} (hu : u ∈ S) :
    bucketRun (S.erase u) quot rem (quot u) =
      (bucketRun S quot rem (quot u)).erase (rem u) := by
  refine List.Perm.eq_of_pairwise'
    (pairwise_le_bucketRun (S.erase u) quot rem (quot u))
    ((pairwise_le_bucketRun S quot rem (quot u)).sublist List.erase_sublist) ?_
  have hfilter : S.filter (fun x => quot x = quot u) =
      insert u ((S.erase u).filter fun x => quot x = quot u) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
    by_cases hxu : x = u
    · subst hxu
      simp [hu]
    · simp [hxu]
  have hu_notMem : u ∉ (S.erase u).filter (fun x => quot x = quot u) := by
    simp
  have hval : ((S.erase u).filter (fun x => quot x = quot u)).val.map rem =
      ((S.filter (fun x => quot x = quot u)).val.map rem).erase (rem u) := by
    conv_rhs => rw [hfilter, Finset.insert_val_of_notMem hu_notMem, Multiset.map_cons,
      Multiset.erase_cons_head]
  dsimp only [bucketRun]
  rw [← Multiset.coe_eq_coe, Multiset.sort_eq, ← Multiset.coe_erase, Multiset.sort_eq, hval]

/-- Tag a bucket's remainder list with `isRunStart` booleans: `true` at the head, `false` at all
subsequent positions. -/
@[expose] def taggedRun {f : ℕ} : List (Fin (2 ^ f)) → List (Bool × Fin (2 ^ f))
  | [] => []
  | r :: rs => (true, r) :: rs.map fun x => (false, x)

@[simp]
theorem taggedRun_nil {f : ℕ} : taggedRun ([] : List (Fin (2 ^ f))) = [] := rfl

@[simp]
theorem taggedRun_cons {f : ℕ} (r : Fin (2 ^ f)) (rs : List (Fin (2 ^ f))) :
    taggedRun (r :: rs) = (true, r) :: rs.map (fun x => (false, x)) := rfl

@[simp]
theorem length_taggedRun {f : ℕ} (xs : List (Fin (2 ^ f))) :
    (taggedRun xs).length = xs.length := by
  cases xs <;> simp [taggedRun]

@[simp]
theorem map_snd_taggedRun {f : ℕ} (xs : List (Fin (2 ^ f))) :
    (taggedRun xs).map Prod.snd = xs := by
  cases xs with
  | nil => rfl
  | cons r rs =>
    simp [taggedRun, List.map_map, Function.comp_def]

theorem taggedRun_eq_nil_iff {f : ℕ} (xs : List (Fin (2 ^ f))) :
    taggedRun xs = [] ↔ xs = [] := by
  cases xs <;> simp [taggedRun]

theorem countP_fst_taggedRun {f : ℕ} (xs : List (Fin (2 ^ f))) :
    (taggedRun xs).countP Prod.fst = if xs = [] then 0 else 1 := by
  cases xs with
  | nil => rfl
  | cons r rs =>
    have hzero : (rs.map (fun x : Fin (2 ^ f) => (false, x))).countP Prod.fst = 0 := by
      induction rs with
      | nil => rfl
      | cons x xs ih => simp [ih]
    simp [taggedRun, hzero]

/-! ## Section 2: Pure filter state and cluster invariants -/

/-- Pure slot-level state of a quotient filter with `2 ^ b` slots and `f`-bit remainders. -/
structure FilterState (b f : ℕ) where
  /-- Whether slot `s` currently holds an element. -/
  isFull : Fin (2 ^ b) → Bool
  /-- Whether bucket `q` currently has a non-empty run. -/
  isOcc : Fin (2 ^ b) → Bool
  /-- Whether slot `s` is the first slot of a bucket's run. -/
  isRunStart : Fin (2 ^ b) → Bool
  /-- Remainder stored at slot `s` (`0` when `isFull s = false`). -/
  remAt : Fin (2 ^ b) → Fin (2 ^ f)

/-- Empty quotient-filter state (all metadata bits `false` and all remainders `0`). -/
@[expose] def FilterState.empty (b f : ℕ) : FilterState b f where
  isFull := fun _ => false
  isOcc := fun _ => false
  isRunStart := fun _ => false
  remAt := fun _ => ⟨0, Nat.two_pow_pos f⟩

/-! ## Section 3: Run offsets, prefix counts, and `IntervalValid` -/

/-- Starting slot offset (relative to cluster start `o`) of bucket `probeSlot b o m`'s run:
the sum of `|bucketRun S quot rem (probeSlot b o j)|` over `j < m`. -/
@[expose] noncomputable def runOffset {U b f : ℕ} (S : Finset (Fin U))
    (quot : Fin U → Fin (2 ^ b)) (rem : Fin U → Fin (2 ^ f)) (o : Fin (2 ^ b)) (m : ℕ) : ℕ :=
  ((List.range m).flatMap fun j => taggedRun (bucketRun S quot rem (probeSlot b o j))).length

@[simp]
theorem runOffset_zero {U b f : ℕ} (S : Finset (Fin U))
    (quot : Fin U → Fin (2 ^ b)) (rem : Fin U → Fin (2 ^ f)) (o : Fin (2 ^ b)) :
    runOffset S quot rem o 0 = 0 := rfl

theorem runOffset_succ {U b f : ℕ} (S : Finset (Fin U))
    (quot : Fin U → Fin (2 ^ b)) (rem : Fin U → Fin (2 ^ f)) (o : Fin (2 ^ b)) (m : ℕ) :
    runOffset S quot rem o (m + 1) =
      runOffset S quot rem o m + (bucketRun S quot rem (probeSlot b o m)).length := by
  simp [runOffset, List.range_succ]

theorem runOffset_mono {U b f : ℕ} (S : Finset (Fin U))
    (quot : Fin U → Fin (2 ^ b)) (rem : Fin U → Fin (2 ^ f)) (o : Fin (2 ^ b))
    {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) :
    runOffset S quot rem o m₁ ≤ runOffset S quot rem o m₂ := by
  induction h with
  | refl => exact le_rfl
  | step _ ih =>
    rw [runOffset_succ]
    omega

/-- Number of occupied buckets (`isOcc = true`) in `[0, m)` relative to `o`. -/
@[expose] def occBefore {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) (m : ℕ) : ℕ :=
  ((List.range m).map fun j => st.isOcc (probeSlot b o j)).countP id

/-- Number of run-start slots (`isRunStart = true`) in `[0, i)` relative to `o`. -/
@[expose] def runsBefore {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) (i : ℕ) : ℕ :=
  ((List.range i).map fun s => st.isRunStart (probeSlot b o s)).countP id

@[simp]
theorem occBefore_zero {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) :
    occBefore st o 0 = 0 := rfl

theorem occBefore_succ {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) (m : ℕ) :
    occBefore st o (m + 1) =
      occBefore st o m + if st.isOcc (probeSlot b o m) then 1 else 0 := by
  simp [occBefore, List.range_succ, List.countP_append]

@[simp]
theorem runsBefore_zero {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) :
    runsBefore st o 0 = 0 := rfl

theorem runsBefore_succ {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) (i : ℕ) :
    runsBefore st o (i + 1) =
      runsBefore st o i + if st.isRunStart (probeSlot b o i) then 1 else 0 := by
  simp [runsBefore, List.range_succ, List.countP_append]

/-- Canonical run decomposition invariant on a full interval `[o .. o + ℓ)`:
1. Every slot in `[o .. o + ℓ)` is full (`isFull = true`).
2. Every prefix `m < ℓ` has `m + 1 ≤ runOffset S quot rem o (m + 1)` (the queue never empties
   inside `[o .. o + ℓ)`).
3. The `ℓ` slots `[o .. o + ℓ)` store the exact concatenation of `taggedRun`s for buckets
   `[o .. o + ℓ)`. -/
structure IntervalValid {U b f : ℕ} (S : Finset (Fin U))
    (quot : Fin U → Fin (2 ^ b)) (rem : Fin U → Fin (2 ^ f))
    (st : FilterState b f) (o : Fin (2 ^ b)) (ℓ : ℕ) : Prop where
  /-- Every slot in `[o .. o + ℓ)` is full. -/
  full_of_lt : ∀ i < ℓ, st.isFull (probeSlot b o i) = true
  /-- Every proper prefix has at least `m + 1` elements from buckets `[0 .. m]`. -/
  prefix_le_runOffset : ∀ m < ℓ, m + 1 ≤ runOffset S quot rem o (m + 1)
  /-- The slot stream `(isRunStart, remAt)` on `[o .. o + ℓ)` equals the concatenated
  `taggedRun`s. -/
  slots_eq_flatMap :
    (List.range ℓ).map (fun i => (st.isRunStart (probeSlot b o i), st.remAt (probeSlot b o i))) =
      (List.range ℓ).flatMap fun j => taggedRun (bucketRun S quot rem (probeSlot b o j))

theorem IntervalValid.runOffset_eq {U b f : ℕ} {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)}
    {st : FilterState b f} {o : Fin (2 ^ b)} {ℓ : ℕ}
    (h : IntervalValid S quot rem st o ℓ) :
    runOffset S quot rem o ℓ = ℓ := by
  dsimp only [runOffset]
  rw [← h.slots_eq_flatMap, List.length_map, List.length_range]

theorem intervalValid_zero {U b f : ℕ} (S : Finset (Fin U))
    (quot : Fin U → Fin (2 ^ b)) (rem : Fin U → Fin (2 ^ f))
    (st : FilterState b f) (o : Fin (2 ^ b)) :
    IntervalValid S quot rem st o 0 where
  full_of_lt i hi := by omega
  prefix_le_runOffset m hm := by omega
  slots_eq_flatMap := rfl

private theorem countP_fst_flatMap_taggedRun {U b f : ℕ} (S : Finset (Fin U))
    (quot : Fin U → Fin (2 ^ b)) (rem : Fin U → Fin (2 ^ f))
    (st : FilterState b f) (o : Fin (2 ^ b)) (m : ℕ)
    (hocc : ∀ j < m,
      st.isOcc (probeSlot b o j) = !(bucketRun S quot rem (probeSlot b o j)).isEmpty) :
    ((List.range m).flatMap fun j =>
      taggedRun (bucketRun S quot rem (probeSlot b o j))).countP Prod.fst =
      occBefore st o m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, List.countP_append,
      ih (fun j hj => hocc j (by omega)), List.flatMap_singleton, countP_fst_taggedRun,
      occBefore_succ, hocc m (by omega)]
    cases hrun : bucketRun S quot rem (probeSlot b o m) <;> simp

private theorem flatMap_taggedRun_split {U b f : ℕ} (S : Finset (Fin U))
    (quot : Fin U → Fin (2 ^ b)) (rem : Fin U → Fin (2 ^ f)) (o : Fin (2 ^ b))
    {m ℓ : ℕ} (hm : m ≤ ℓ) :
    ((List.range ℓ).flatMap fun j => taggedRun (bucketRun S quot rem (probeSlot b o j))) =
      ((List.range m).flatMap fun j => taggedRun (bucketRun S quot rem (probeSlot b o j))) ++
      (((List.range (ℓ - m)).map (m + ·)).flatMap fun j =>
        taggedRun (bucketRun S quot rem (probeSlot b o j))) := by
  have hr : List.range ℓ = List.range m ++ (List.range (ℓ - m)).map (m + ·) := by
    rw [← List.range_add, Nat.add_sub_of_le hm]
  conv_lhs => rw [hr, List.flatMap_append]

/-- The first element of any non-empty concatenation of `taggedRun`s has `isRunStart` tag `true`. -/
theorem fst_head_nonempty_flatMap_taggedRun {α : Type*} {f : ℕ}
    (xs : List α) (g : α → List (Fin (2 ^ f))) {p : Bool × Fin (2 ^ f)}
    {rest : List (Bool × Fin (2 ^ f))}
    (h : xs.flatMap (fun a => taggedRun (g a)) = p :: rest) :
    p.1 = true := by
  induction xs with
  | nil => simp at h
  | cons a xs ih =>
    simp only [List.flatMap_cons] at h
    cases hga : g a with
    | nil =>
      simp only [hga, taggedRun_nil, List.nil_append] at h
      exact ih h
    | cons r rs =>
      simp only [hga, taggedRun_cons, List.cons_append, List.cons.injEq] at h
      rw [← h.1]

/-- **Master run-offset threshold theorem**: in any valid interval `[o .. o + ℓ)`, for every
bucket index `m ≤ ℓ` and slot index `i < ℓ`, slot `i` lies strictly before bucket `m`'s run start
`runOffset S quot rem o m` if and only if `runsBefore st o (i + 1) ≤ occBefore st o m`. -/
theorem IntervalValid.lt_runOffset_iff {U b f : ℕ} {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)}
    {st : FilterState b f} {o : Fin (2 ^ b)} {ℓ : ℕ}
    (hinv : IntervalValid S quot rem st o ℓ)
    (hocc : ∀ q : Fin (2 ^ b), st.isOcc q = !(bucketRun S quot rem q).isEmpty)
    {m i : ℕ} (hm : m ≤ ℓ) (hi : i < ℓ) :
    i < runOffset S quot rem o m ↔ runsBefore st o (i + 1) ≤ occBefore st o m := by
  set stream :=
    (List.range ℓ).flatMap fun j => taggedRun (bucketRun S quot rem (probeSlot b o j))
  set pref :=
    (List.range m).flatMap fun j => taggedRun (bucketRun S quot rem (probeSlot b o j))
  set suff :=
    ((List.range (ℓ - m)).map (m + ·)).flatMap fun j =>
      taggedRun (bucketRun S quot rem (probeSlot b o j))
  have hstream_eq : stream = pref ++ suff := flatMap_taggedRun_split S quot rem o hm
  have hpref_len : pref.length = runOffset S quot rem o m := rfl
  have hstream_len : stream.length = ℓ := hinv.runOffset_eq
  have hruns_eq : runsBefore st o (i + 1) = (stream.take (i + 1)).countP Prod.fst := by
    have hmap_fst :
        ((List.range ℓ).map fun s => st.isRunStart (probeSlot b o s)) =
          stream.map Prod.fst := by
      have := congrArg (List.map Prod.fst) hinv.slots_eq_flatMap
      simpa [List.map_map, Function.comp_def] using this
    have htake :
        ((List.range (i + 1)).map fun s => st.isRunStart (probeSlot b o s)) =
          (stream.take (i + 1)).map Prod.fst := by
      have hr : List.range (i + 1) = (List.range ℓ).take (i + 1) := by
        rw [List.take_range, Nat.min_eq_left (by omega)]
      rw [hr, List.map_take, hmap_fst, ← List.map_take]
    dsimp only [runsBefore]
    rw [htake, List.countP_map]
    rfl
  have hpref_count : pref.countP Prod.fst = occBefore st o m :=
    countP_fst_flatMap_taggedRun S quot rem st o m (fun j _ => hocc _)
  rw [hruns_eq, ← hpref_count]
  constructor
  · intro hlt
    have hi1_le : i + 1 ≤ pref.length := by omega
    rw [hstream_eq, List.take_append_of_le_length hi1_le]
    have hsplit : pref = pref.take (i + 1) ++ pref.drop (i + 1) :=
      (List.take_append_drop (i + 1) pref).symm
    conv_rhs => rw [hsplit, List.countP_append]
    omega
  · intro hle
    by_contra! hge
    have hlen_lt : pref.length < stream.length := by omega
    have hsuff_ne : suff ≠ [] := by
      intro hnil
      rw [hstream_eq, hnil, List.append_nil] at hlen_lt
      exact Nat.lt_irrefl _ hlen_lt
    obtain ⟨p, rest, hsuff_cons⟩ := List.exists_cons_of_ne_nil hsuff_ne
    have hp_fst : p.1 = true :=
      fst_head_nonempty_flatMap_taggedRun ((List.range (ℓ - m)).map (m + ·))
        (fun j => bucketRun S quot rem (probeSlot b o j)) hsuff_cons
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i + 1 - pref.length ≠ 0)
    have hi1_eq : i + 1 = pref.length + (k + 1) := by omega
    rw [hstream_eq, hsuff_cons, hi1_eq, List.take_append, Nat.add_sub_cancel_left,
      List.take_of_length_le (by omega : pref.length ≤ pref.length + (k + 1)),
      List.take_succ_cons, List.countP_append, List.countP_cons, hp_fst] at hle
    simp at hle

/-- In any valid interval `[o .. o + ℓ)`, for every `m ≤ ℓ` we have
`m ≤ runOffset S quot rem o m`. -/
theorem IntervalValid.le_runOffset {U b f : ℕ} {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)}
    {st : FilterState b f} {o : Fin (2 ^ b)} {ℓ : ℕ}
    (hinv : IntervalValid S quot rem st o ℓ) {m : ℕ} (hm : m ≤ ℓ) :
    m ≤ runOffset S quot rem o m := by
  cases m with
  | zero => simp
  | succ m => exact hinv.prefix_le_runOffset m (by omega)

/-- In any valid interval `[o .. o + ℓ)`, `runsBefore st o m ≤ occBefore st o m` holds at every
step `m ≤ ℓ` (so `occBefore st o m - runsBefore st o m` never underflows). -/
theorem IntervalValid.runsBefore_le_occBefore {U b f : ℕ} {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)}
    {st : FilterState b f} {o : Fin (2 ^ b)} {ℓ : ℕ}
    (hinv : IntervalValid S quot rem st o ℓ)
    (hocc : ∀ q : Fin (2 ^ b), st.isOcc q = !(bucketRun S quot rem q).isEmpty)
    {m : ℕ} (hm : m ≤ ℓ) :
    runsBefore st o m ≤ occBefore st o m := by
  cases m with
  | zero => simp
  | succ m =>
    have hlt : m < runOffset S quot rem o (m + 1) := by
      have := hinv.prefix_le_runOffset m (by omega)
      omega
    exact (hinv.lt_runOffset_iff hocc hm (by omega)).mp hlt

/-- Exact characterization of when `runOffset S quot rem o m = m` in `[o .. o + ℓ)`:
`runOffset S quot rem o m = m ↔ (m = ℓ ∨ occBefore st o m < runsBefore st o (m + 1))`. -/
theorem IntervalValid.runOffset_eq_self_iff {U b f : ℕ} {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)}
    {st : FilterState b f} {o : Fin (2 ^ b)} {ℓ : ℕ}
    (hinv : IntervalValid S quot rem st o ℓ)
    (hocc : ∀ q : Fin (2 ^ b), st.isOcc q = !(bucketRun S quot rem q).isEmpty)
    {m : ℕ} (hm : m ≤ ℓ) :
    runOffset S quot rem o m = m ↔ (m = ℓ ∨ occBefore st o m < runsBefore st o (m + 1)) := by
  have hge : m ≤ runOffset S quot rem o m := hinv.le_runOffset hm
  rcases eq_or_lt_of_le hm with rfl | hlt
  · simp [hinv.runOffset_eq]
  · have hiff := hinv.lt_runOffset_iff hocc hm hlt
    omega

/-! ## Section 4: Global filter invariant, cluster bounds, and scale-overload witness -/

/-- Canonical quotient-filter invariant coupling key set `S : Finset (Fin U)`, quotient hash
`quot : Fin U → Fin (2 ^ b)`, and remainder hash `rem : Fin U → Fin (2 ^ f)` with slot state
`st : FilterState b f`:
1. `#S ≤ n`;
2. `st.isOcc q = !(bucketRun S quot rem q).isEmpty` for all `q`;
3. every empty slot (`st.isFull q = false`) has `st.isOcc q = false`, `st.isRunStart q = false`,
   and `st.remAt q = 0`;
4. the number of full slots in `Fin (2 ^ b)` equals `#S`;
5. every maximal contiguous full interval `[o .. o + ℓ)` satisfies `IntervalValid`. -/
structure FilterInv {U b f : ℕ} (n : ℕ) (S : Finset (Fin U))
    (quot : Fin U → Fin (2 ^ b)) (rem : Fin U → Fin (2 ^ f))
    (st : FilterState b f) : Prop where
  /-- Current key set has size at most `n`. -/
  card_le : #S ≤ n
  /-- `isOcc q` records whether bucket `q`'s run is non-empty. -/
  isOcc_eq : ∀ q : Fin (2 ^ b), st.isOcc q = !(bucketRun S quot rem q).isEmpty
  /-- Empty slots have cleared metadata and zero remainder. -/
  empty_slot : ∀ q : Fin (2 ^ b), st.isFull q = false →
    st.isOcc q = false ∧ st.isRunStart q = false ∧ st.remAt q = ⟨0, Nat.two_pow_pos f⟩
  /-- Total number of full slots equals `#S`. -/
  card_full_eq : #(Finset.univ.filter fun q : Fin (2 ^ b) => st.isFull q = true) = #S
  /-- Every maximal full interval satisfies `IntervalValid`. -/
  maximal_intervalValid : ∀ (o : Fin (2 ^ b)) (ℓ : ℕ),
    ℓ ≤ #S →
    st.isFull (backSlot b o 1) = false →
    st.isFull (probeSlot b o ℓ) = false →
    (∀ i < ℓ, st.isFull (probeSlot b o i) = true) →
    IntervalValid S quot rem st o ℓ

/-- The empty state `FilterState.empty b f` satisfies `FilterInv` for `S = ∅`. -/
theorem filterInv_empty {U b f : ℕ} (n : ℕ)
    (quot : Fin U → Fin (2 ^ b)) (rem : Fin U → Fin (2 ^ f)) :
    FilterInv n (∅ : Finset (Fin U)) quot rem (FilterState.empty b f) where
  card_le := by simp
  isOcc_eq q := by simp [FilterState.empty]
  empty_slot q _ := ⟨rfl, rfl, rfl⟩
  card_full_eq := by simp [FilterState.empty]
  maximal_intervalValid o ℓ hℓ _ _ _ := by
    have h0 : ℓ = 0 := by simpa using hℓ
    subst h0
    exact intervalValid_zero ∅ quot rem (FilterState.empty b f) o

/-- Any finset of full slots has cardinality at most `#S`. -/
theorem FilterInv.card_full_slots_le {U b f n : ℕ} {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)} {st : FilterState b f}
    (hinv : FilterInv n S quot rem st) (A : Finset (Fin (2 ^ b)))
    (hfull : ∀ q ∈ A, st.isFull q = true) :
    #A ≤ #S := by
  rw [← hinv.card_full_eq]
  refine Finset.card_le_card fun q hq => ?_
  simp [hfull q hq]

/-- Under `FilterInv` with `#S < 2 ^ b`, walking backwards from any `q` reaches an empty slot
within `#S + 1` steps. -/
theorem FilterInv.exists_backSlot_empty {U b f n : ℕ} {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)} {st : FilterState b f}
    (hinv : FilterInv n S quot rem st) (hS_lt : #S < 2 ^ b) (q : Fin (2 ^ b)) :
    ∃ r, r ≤ #S ∧ st.isFull (backSlot b q (r + 1)) = false := by
  by_contra! hall
  set A := (Finset.range (#S + 1)).image (probeSlot b (backSlot b q (#S + 1)))
  have hcardA : #A = #S + 1 := by
    rw [Finset.card_image_of_injOn (probeSlot_injOn_range _ (by omega)), Finset.card_range]
  have hle : #A ≤ #S := by
    refine hinv.card_full_slots_le A fun p hp => ?_
    obtain ⟨idx, hidx, rfl⟩ := Finset.mem_image.mp hp
    have hidx_lt : idx < #S + 1 := Finset.mem_range.mp hidx
    rw [probeSlot_backSlot_sub q (by omega)]
    have hsub : #S + 1 - idx = (#S - idx) + 1 := by omega
    rw [hsub]
    exact Bool.eq_true_of_not_eq_false (hall (#S - idx) (by omega))
  omega

/-- Number of full slots immediately preceding `q` in cyclic order. -/
@[expose] noncomputable def FilterInv.backLen {U b f n : ℕ} {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)} {st : FilterState b f}
    (hinv : FilterInv n S quot rem st) (hS_lt : #S < 2 ^ b) (q : Fin (2 ^ b)) : ℕ :=
  Nat.find (hinv.exists_backSlot_empty hS_lt q)

theorem FilterInv.backLen_le_card {U b f n : ℕ} {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)} {st : FilterState b f}
    (hinv : FilterInv n S quot rem st) (hS_lt : #S < 2 ^ b) (q : Fin (2 ^ b)) :
    hinv.backLen hS_lt q ≤ #S :=
  (Nat.find_spec (hinv.exists_backSlot_empty hS_lt q)).1

theorem FilterInv.isFull_backSlot_succ_backLen {U b f n : ℕ} {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)} {st : FilterState b f}
    (hinv : FilterInv n S quot rem st) (hS_lt : #S < 2 ^ b) (q : Fin (2 ^ b)) :
    st.isFull (backSlot b q (hinv.backLen hS_lt q + 1)) = false :=
  (Nat.find_spec (hinv.exists_backSlot_empty hS_lt q)).2

theorem FilterInv.isFull_backSlot_of_le_backLen {U b f n : ℕ} {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)} {st : FilterState b f}
    (hinv : FilterInv n S quot rem st) (hS_lt : #S < 2 ^ b) (q : Fin (2 ^ b))
    {r : ℕ} (hr1 : 1 ≤ r) (hr : r ≤ hinv.backLen hS_lt q) :
    st.isFull (backSlot b q r) = true := by
  have hlt : r - 1 < hinv.backLen hS_lt q := by omega
  have hmin := Nat.find_min (hinv.exists_backSlot_empty hS_lt q) hlt
  push Not at hmin
  have hle : r - 1 ≤ #S := by
    have := hinv.backLen_le_card hS_lt q
    omega
  have hne := hmin hle
  rw [Nat.sub_add_cancel hr1] at hne
  exact Bool.eq_true_of_not_eq_false hne

/-- Start slot `o = backSlot b q (backLen q)` of the full cluster around `q`. -/
@[expose] noncomputable def FilterInv.clusterStart {U b f n : ℕ} {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)} {st : FilterState b f}
    (hinv : FilterInv n S quot rem st) (hS_lt : #S < 2 ^ b) (q : Fin (2 ^ b)) : Fin (2 ^ b) :=
  backSlot b q (hinv.backLen hS_lt q)

/-- Under `FilterInv` with `#S < 2 ^ b`, walking forward from `q` reaches an empty slot within
`#S - backLen q` steps. -/
theorem FilterInv.exists_probeSlot_empty {U b f n : ℕ} {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)} {st : FilterState b f}
    (hinv : FilterInv n S quot rem st) (hS_lt : #S < 2 ^ b) (q : Fin (2 ^ b)) :
    ∃ t, t ≤ #S - hinv.backLen hS_lt q ∧ st.isFull (probeSlot b q t) = false := by
  by_contra! hall
  set a := hinv.backLen hS_lt q
  have ha_le : a ≤ #S := hinv.backLen_le_card hS_lt q
  set o := hinv.clusterStart hS_lt q
  set A := (Finset.range (#S + 1)).image (probeSlot b o)
  have hcardA : #A = #S + 1 := by
    rw [Finset.card_image_of_injOn (probeSlot_injOn_range o (by omega)), Finset.card_range]
  have hle : #A ≤ #S := by
    refine hinv.card_full_slots_le A fun p hp => ?_
    obtain ⟨idx, hidx, rfl⟩ := Finset.mem_image.mp hp
    have hidx_lt : idx < #S + 1 := Finset.mem_range.mp hidx
    by_cases hlt : idx < a
    · dsimp only [o, clusterStart]
      rw [probeSlot_backSlot_sub q (by omega)]
      exact hinv.isFull_backSlot_of_le_backLen hS_lt q (by omega) (by omega)
    · dsimp only [o, clusterStart]
      have heq : idx = a + (idx - a) := by omega
      rw [heq, probeSlot_backSlot_add]
      exact Bool.eq_true_of_not_eq_false (hall (idx - a) (by omega))
  omega

/-- Number of full slots starting at `q` in cyclic forward order. -/
@[expose] noncomputable def FilterInv.fwdLen {U b f n : ℕ} {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)} {st : FilterState b f}
    (hinv : FilterInv n S quot rem st) (hS_lt : #S < 2 ^ b) (q : Fin (2 ^ b)) : ℕ :=
  Nat.find (hinv.exists_probeSlot_empty hS_lt q)

theorem FilterInv.fwdLen_le_sub {U b f n : ℕ} {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)} {st : FilterState b f}
    (hinv : FilterInv n S quot rem st) (hS_lt : #S < 2 ^ b) (q : Fin (2 ^ b)) :
    hinv.fwdLen hS_lt q ≤ #S - hinv.backLen hS_lt q :=
  (Nat.find_spec (hinv.exists_probeSlot_empty hS_lt q)).1

/-- Total length `ℓ = backLen q + fwdLen q` of the maximal full cluster around `q`. -/
@[expose] noncomputable def FilterInv.clusterLen {U b f n : ℕ} {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)} {st : FilterState b f}
    (hinv : FilterInv n S quot rem st) (hS_lt : #S < 2 ^ b) (q : Fin (2 ^ b)) : ℕ :=
  hinv.backLen hS_lt q + hinv.fwdLen hS_lt q

theorem FilterInv.clusterLen_le_card {U b f n : ℕ} {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)} {st : FilterState b f}
    (hinv : FilterInv n S quot rem st) (hS_lt : #S < 2 ^ b) (q : Fin (2 ^ b)) :
    hinv.clusterLen hS_lt q ≤ #S := by
  have h1 := hinv.backLen_le_card hS_lt q
  have h2 := hinv.fwdLen_le_sub hS_lt q
  dsimp only [clusterLen]
  omega

theorem FilterInv.isFull_probeSlot_fwdLen {U b f n : ℕ} {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)} {st : FilterState b f}
    (hinv : FilterInv n S quot rem st) (hS_lt : #S < 2 ^ b) (q : Fin (2 ^ b)) :
    st.isFull (probeSlot b q (hinv.fwdLen hS_lt q)) = false :=
  (Nat.find_spec (hinv.exists_probeSlot_empty hS_lt q)).2

theorem FilterInv.isFull_probeSlot_of_lt_fwdLen {U b f n : ℕ} {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)} {st : FilterState b f}
    (hinv : FilterInv n S quot rem st) (hS_lt : #S < 2 ^ b) (q : Fin (2 ^ b))
    {d : ℕ} (hd : d < hinv.fwdLen hS_lt q) :
    st.isFull (probeSlot b q d) = true := by
  have hmin := Nat.find_min (hinv.exists_probeSlot_empty hS_lt q) hd
  push Not at hmin
  have h2 := hinv.fwdLen_le_sub hS_lt q
  exact Bool.eq_true_of_not_eq_false (hmin (by omega))

/-- The maximal full cluster `[clusterStart q .. clusterStart q + clusterLen q)` around any bucket
`q` satisfies `IntervalValid`. -/
theorem FilterInv.intervalValid_cluster {U b f n : ℕ} {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)} {st : FilterState b f}
    (hinv : FilterInv n S quot rem st) (hS_lt : #S < 2 ^ b) (q : Fin (2 ^ b)) :
    IntervalValid S quot rem st (hinv.clusterStart hS_lt q) (hinv.clusterLen hS_lt q) := by
  refine hinv.maximal_intervalValid (hinv.clusterStart hS_lt q) (hinv.clusterLen hS_lt q)
    (hinv.clusterLen_le_card hS_lt q) ?_ ?_ ?_
  · dsimp only [clusterStart]
    rw [backSlot_backSlot]
    exact hinv.isFull_backSlot_succ_backLen hS_lt q
  · dsimp only [clusterStart, clusterLen]
    rw [probeSlot_backSlot_add]
    exact hinv.isFull_probeSlot_fwdLen hS_lt q
  · intro i hi
    dsimp only [clusterStart, clusterLen] at hi ⊢
    by_cases hlt : i < hinv.backLen hS_lt q
    · rw [probeSlot_backSlot_sub q (by omega)]
      exact hinv.isFull_backSlot_of_le_backLen hS_lt q (by omega) (by omega)
    · have heq : i = hinv.backLen hS_lt q + (i - hinv.backLen hS_lt q) := by omega
      rw [heq, probeSlot_backSlot_add]
      exact hinv.isFull_probeSlot_of_lt_fwdLen hS_lt q (by omega)

private theorem runOffset_eq_card_filter_image {U b f : ℕ} (S : Finset (Fin U))
    (quot : Fin U → Fin (2 ^ b)) (rem : Fin U → Fin (2 ^ f)) (o : Fin (2 ^ b))
    {m : ℕ} (hm : m ≤ 2 ^ b) :
    runOffset S quot rem o m =
      #(S.filter fun x => quot x ∈ (Finset.range m).image (probeSlot b o)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [runOffset_succ, ih (by omega), length_bucketRun, Finset.range_add_one, Finset.image_insert]
    have hnotMem : probeSlot b o m ∉ (Finset.range m).image (probeSlot b o) := by
      intro hmem
      obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hmem
      have hj_lt : j < m := Finset.mem_range.mp hj
      have hinj := probeSlot_injOn_range o hm
        (Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)))
        (Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega))) heq
      omega
    have hfilter_union :
        (S.filter fun x =>
          quot x ∈ insert (probeSlot b o m) ((Finset.range m).image (probeSlot b o))) =
        (S.filter fun x => quot x ∈ (Finset.range m).image (probeSlot b o)) ∪
          (S.filter fun x => quot x = probeSlot b o m) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_union]
      tauto
    have hdisj : Disjoint
        (S.filter fun x => quot x ∈ (Finset.range m).image (probeSlot b o))
        (S.filter fun x => quot x = probeSlot b o m) := by
      rw [Finset.disjoint_filter]
      intro x _ hmem heq
      exact hnotMem (heq ▸ hmem)
    rw [hfilter_union, Finset.card_union_of_disjoint hdisj]

/-- **Exact cluster occupancy identity**: the number of keys in `S` whose quotient lies in the
maximal full cluster `cyclicInterval b q (backLen q) (clusterLen q)` around `q` equals
`clusterLen q`. -/
theorem FilterInv.card_filter_quot_mem_cyclicInterval_eq {U b f n : ℕ} {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)} {st : FilterState b f}
    (hinv : FilterInv n S quot rem st) (hS_lt : #S < 2 ^ b) (q : Fin (2 ^ b)) :
    #(S.filter fun x =>
      quot x ∈ cyclicInterval b q (hinv.backLen hS_lt q) (hinv.clusterLen hS_lt q)) =
      hinv.clusterLen hS_lt q := by
  have hvalid := hinv.intervalValid_cluster hS_lt q
  have hlen_le : hinv.clusterLen hS_lt q ≤ 2 ^ b :=
    (hinv.clusterLen_le_card hS_lt q).trans hS_lt.le
  rw [cyclicInterval_eq_image_probeSlot]
  change #(S.filter fun x =>
    quot x ∈ (Finset.range (hinv.clusterLen hS_lt q)).image
      (probeSlot b (hinv.clusterStart hS_lt q))) = hinv.clusterLen hS_lt q
  rw [← runOffset_eq_card_filter_image S quot rem _ hlen_le, hvalid.runOffset_eq]

/-- **Pointwise dyadic scale-overload bound for quotient-filter clusters**: for any hash family
`h : Θ → Fin U₀ → Fin (2 ^ b₀)`, seed `i : Θ`, and key `u : Fin U₀`, the cluster length minus one
`(hinv.clusterLen hS_lt (h i u) - 1 : ℝ)` is bounded by the dyadic scale-overload sum for
`S.erase u` around `h i u`. -/
theorem FilterInv.clusterLen_sub_one_le_sum_scaleOverload
    {Θ : Type*} {U₀ b₀ f₀ n₀ : ℕ} {S : Finset (Fin U₀)}
    (h : Θ → Fin U₀ → Fin (2 ^ b₀)) (i : Θ) {rem : Fin U₀ → Fin (2 ^ f₀)}
    {st : FilterState b₀ f₀}
    (hinv : FilterInv n₀ S (h i) rem st) (hS_lt : #S < 2 ^ b₀) (u : Fin U₀) :
    ((hinv.clusterLen hS_lt (h i u) - 1 : ℕ) : ℝ) ≤
      ∑ j ∈ Finset.Icc 1 b₀,
        (2 ^ j : ℝ) * (if scaleOverload b₀ h (S.erase u) u j i then (1 : ℝ) else 0) := by
  set q := h i u
  set a := hinv.backLen hS_lt q
  set t := hinv.fwdLen hS_lt q
  set ℓ := hinv.clusterLen hS_lt q
  set k₀ := ℓ - 1
  have hℓ_eq : ℓ = a + t := rfl
  have hℓ_le_S : ℓ ≤ #S := hinv.clusterLen_le_card hS_lt q
  have hcard_J : #(S.filter fun x => h i x ∈ cyclicInterval b₀ q a ℓ) = ℓ :=
    hinv.card_filter_quot_mem_cyclicInterval_eq hS_lt q
  -- A single overloaded scale `r` with `k₀ ≤ 2 ^ r` already bounds `k₀` by the sum.
  have key : ∀ r ∈ Finset.Icc 1 b₀, k₀ ≤ 2 ^ r → scaleOverload b₀ h (S.erase u) u r i →
      (k₀ : ℝ) ≤ ∑ r ∈ Finset.Icc 1 b₀,
        (2 ^ r : ℝ) * (if scaleOverload b₀ h (S.erase u) u r i then (1 : ℝ) else 0) := by
    intro r hr hk_le hov
    calc (k₀ : ℝ) ≤ (2 ^ r : ℝ) := by exact_mod_cast hk_le
      _ = (2 ^ r : ℝ) * (if scaleOverload b₀ h (S.erase u) u r i then (1 : ℝ) else 0) := by
          simp [hov]
      _ ≤ _ := by
          refine Finset.single_le_sum
            (f := fun r =>
              (2 ^ r : ℝ) * (if scaleOverload b₀ h (S.erase u) u r i then (1 : ℝ) else 0))
            (fun r _ => ?_) hr
          split_ifs <;> positivity
  by_cases hk₀ : 1 ≤ k₀
  · by_cases ht_pos : 1 ≤ t
    · set j := Nat.log 2 k₀ + 1
      have hj_ge_one : 1 ≤ j := Nat.le_add_left 1 _
      have h2j1_le : 2 ^ (j - 1) ≤ k₀ := Nat.pow_log_le_self 2 (by omega)
      have hk₀_lt_2j : k₀ < 2 ^ j := Nat.lt_pow_succ_log_self (by decide) k₀
      have hℓ_le_2j : ℓ ≤ 2 ^ j := by omega
      have ha_lt_2j : a < 2 ^ j := by omega
      have hj_le_b : j ≤ b₀ := by
        have hpow_lt : 2 ^ (j - 1) < 2 ^ b₀ := by omega
        have hj1_lt : j - 1 < b₀ := (Nat.pow_lt_pow_iff_right (by decide)).mp hpow_lt
        omega
      have hj_mem : j ∈ Finset.Icc 1 b₀ := Finset.mem_Icc.mpr ⟨hj_ge_one, hj_le_b⟩
      have hov : scaleOverload b₀ h (S.erase u) u j i := by
        dsimp only [scaleOverload]
        change 2 ^ (j - 1) ≤ #((S.erase u).filter fun x => h i x ∈ scaleWindow b₀ q j)
        have hsub : cyclicInterval b₀ q a ℓ ⊆ scaleWindow b₀ q j :=
          cyclicInterval_subset_scaleWindow q ha_lt_2j hℓ_le_2j
        have herase_card :
            ℓ - 1 ≤ #((S.erase u).filter fun x => h i x ∈ cyclicInterval b₀ q a ℓ) := by
          have h1 : (S.erase u).filter (fun x => h i x ∈ cyclicInterval b₀ q a ℓ) =
              (S.filter fun x => h i x ∈ cyclicInterval b₀ q a ℓ).erase u := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_erase]
            tauto
          rw [h1]
          have hpred :
              #(S.filter fun x => h i x ∈ cyclicInterval b₀ q a ℓ) - 1 ≤
                #((S.filter fun x => h i x ∈ cyclicInterval b₀ q a ℓ).erase u) :=
            Finset.pred_card_le_card_erase
          omega
        have hfilter :
            #((S.erase u).filter fun x => h i x ∈ cyclicInterval b₀ q a ℓ) ≤
              #((S.erase u).filter fun x => h i x ∈ scaleWindow b₀ q j) := by
          refine Finset.card_le_card fun x hx => ?_
          simp only [Finset.mem_filter] at hx ⊢
          exact ⟨hx.1, hsub hx.2⟩
        omega
      exact key j hj_mem hk₀_lt_2j.le hov
    · have ht0 : t = 0 := by omega
      have hfull_q : st.isFull q = false := by
        have h1 := hinv.isFull_probeSlot_fwdLen hS_lt q
        change st.isFull (probeSlot b₀ q t) = false at h1
        rw [ht0, probeSlot_zero] at h1
        exact h1
      have hocc_q : st.isOcc q = false := (hinv.empty_slot q hfull_q).1
      have hu_notMem : u ∉ S := by
        intro hu_mem
        have hrun_ne : bucketRun S (h i) rem q ≠ [] := by
          intro hnil
          have := (bucketRun_eq_nil_iff S (h i) rem q).mp hnil u hu_mem
          exact this rfl
        have hocc_true : st.isOcc q = true := by
          rw [hinv.isOcc_eq q]
          cases h : bucketRun S (h i) rem q
          · exact absurd h hrun_ne
          · rfl
        rw [hocc_q] at hocc_true
        cases hocc_true
      have herase_eq : S.erase u = S := Finset.erase_eq_of_notMem hu_notMem
      set j := Nat.log 2 ℓ + 1
      have hj_ge_one : 1 ≤ j := Nat.le_add_left 1 _
      have h2j1_le : 2 ^ (j - 1) ≤ ℓ := Nat.pow_log_le_self 2 (by omega)
      have hℓ_lt_2j : ℓ < 2 ^ j := Nat.lt_pow_succ_log_self (by decide) ℓ
      have ha_lt_2j : a < 2 ^ j := by omega
      have hj_le_b : j ≤ b₀ := by
        have hpow_lt : 2 ^ (j - 1) < 2 ^ b₀ := by omega
        have hj1_lt : j - 1 < b₀ := (Nat.pow_lt_pow_iff_right (by decide)).mp hpow_lt
        omega
      have hj_mem : j ∈ Finset.Icc 1 b₀ := Finset.mem_Icc.mpr ⟨hj_ge_one, hj_le_b⟩
      have hov : scaleOverload b₀ h (S.erase u) u j i := by
        dsimp only [scaleOverload]
        rw [herase_eq]
        change 2 ^ (j - 1) ≤ #(S.filter fun x => h i x ∈ scaleWindow b₀ q j)
        have hsub : cyclicInterval b₀ q a ℓ ⊆ scaleWindow b₀ q j :=
          cyclicInterval_subset_scaleWindow q ha_lt_2j hℓ_lt_2j.le
        have hfilter :
            #(S.filter fun x => h i x ∈ cyclicInterval b₀ q a ℓ) ≤
              #(S.filter fun x => h i x ∈ scaleWindow b₀ q j) := by
          refine Finset.card_le_card fun x hx => ?_
          simp only [Finset.mem_filter] at hx ⊢
          exact ⟨hx.1, hsub hx.2⟩
        omega
      exact key j hj_mem (by omega) hov
  · have hk0 : k₀ = 0 := by omega
    rw [hk0, Nat.cast_zero]
    refine Finset.sum_nonneg fun r _ => ?_
    split_ifs <;> positivity

/-! ## Section 5: Pure membership query and fingerprint-collision characterization -/

/-- Prefix scan over `m < i` checking whether any slot in bucket `a`'s run
(`occBefore st o a < runsBefore st o (m + 1) ≤ occBefore st o (a + 1)`) stores remainder `r`. -/
@[expose] def queryAnyPrefix {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b))
    (a i : ℕ) (r : Fin (2 ^ f)) : Bool :=
  (List.range i).any fun m =>
    decide (occBefore st o a < runsBefore st o (m + 1) ∧
      runsBefore st o (m + 1) ≤ occBefore st o (a + 1)) &&
    decide (st.remAt (probeSlot b o m) = r)

/-- Pure membership query on `st : FilterState b f` for quotient `q` and remainder `r` in a cluster
starting at `o` with offset `a` (`q = probeSlot b o a`) and length `ℓ`:
checks `st.isOcc q = true` and `queryAnyPrefix st o a ℓ r`. -/
@[expose] def queryCluster {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) (a ℓ : ℕ)
    (r : Fin (2 ^ f)) : Bool :=
  st.isOcc (probeSlot b o a) && queryAnyPrefix st o a ℓ r

/-- In any valid interval `[o .. o + ℓ)` with `a < ℓ`, `queryCluster st o a ℓ r = true` if and only
if `r ∈ bucketRun S quot rem (probeSlot b o a)`. -/
theorem IntervalValid.queryCluster_eq_true_iff {U b f : ℕ} {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)}
    {st : FilterState b f} {o : Fin (2 ^ b)} {ℓ : ℕ}
    (hinv : IntervalValid S quot rem st o ℓ)
    (hocc : ∀ q : Fin (2 ^ b), st.isOcc q = !(bucketRun S quot rem q).isEmpty)
    {a : ℕ} (ha : a < ℓ) (r : Fin (2 ^ f)) :
    queryCluster st o a ℓ r = true ↔ r ∈ bucketRun S quot rem (probeSlot b o a) := by
  have ha1 : a + 1 ≤ ℓ := by omega
  have hrem_list :
      (List.range ℓ).map (fun i => st.remAt (probeSlot b o i)) =
        (List.range ℓ).flatMap (fun j => bucketRun S quot rem (probeSlot b o j)) := by
    have := congrArg (List.map Prod.snd) hinv.slots_eq_flatMap
    simpa [List.map_map, Function.comp_def, List.map_flatMap, map_snd_taggedRun] using this
  set S_a := runOffset S quot rem o a
  set S_a1 := runOffset S quot rem o (a + 1)
  have hS_a1_eq : S_a1 = S_a + (bucketRun S quot rem (probeSlot b o a)).length :=
    runOffset_succ S quot rem o a
  have hS_a1_le : S_a1 ≤ ℓ := by
    rw [← hinv.runOffset_eq]
    exact runOffset_mono S quot rem o ha1
  have hslice :
      (((List.range ℓ).map (fun i => st.remAt (probeSlot b o i))).drop S_a).take
          (bucketRun S quot rem (probeSlot b o a)).length =
        bucketRun S quot rem (probeSlot b o a) := by
    have hr :
        List.range ℓ = List.range a ++ (a :: (List.range (ℓ - (a + 1))).map (a + 1 + ·)) := by
      have h1 :
          List.range ℓ = List.range (a + 1) ++ (List.range (ℓ - (a + 1))).map (a + 1 + ·) := by
        rw [← List.range_add, Nat.add_sub_of_le ha1]
      rw [h1, List.range_succ, List.append_assoc, List.singleton_append]
    rw [hrem_list, hr, List.flatMap_append, List.flatMap_cons]
    have hlen_pref :
        ((List.range a).flatMap (fun j => bucketRun S quot rem (probeSlot b o j))).length =
          S_a := by
      have hmap :
          (List.range a).flatMap (fun j => bucketRun S quot rem (probeSlot b o j)) =
            ((List.range a).flatMap
              (fun j => taggedRun (bucketRun S quot rem (probeSlot b o j)))).map Prod.snd := by
        simp [List.map_flatMap, map_snd_taggedRun]
      rw [hmap, List.length_map]
      rfl
    rw [← hlen_pref, List.drop_append_of_le_length le_rfl, List.drop_length,
      List.nil_append, List.take_append_of_le_length le_rfl, List.take_length]
  constructor
  · intro hq
    simp only [queryCluster, queryAnyPrefix, Bool.and_eq_true, List.any_eq_true, List.mem_range,
      decide_eq_true_eq] at hq
    obtain ⟨_, i, hi_lt, ⟨hi_gt, hi_le⟩, rfl⟩ := hq
    have hge_Sa : S_a ≤ i := by
      have hiff := hinv.lt_runOffset_iff hocc (by omega : a ≤ ℓ) hi_lt
      omega
    have hlt_Sa1 : i < S_a1 := (hinv.lt_runOffset_iff hocc ha1 hi_lt).mpr hi_le
    rw [← hslice]
    set xs := (List.range ℓ).map (fun s => st.remAt (probeSlot b o s))
    have hlen_xs : xs.length = ℓ := by simp [xs]
    have hlen_take : ((xs.drop S_a).take (S_a1 - S_a)).length = S_a1 - S_a := by
      rw [List.length_take, List.length_drop, hlen_xs]
      omega
    have hmem : st.remAt (probeSlot b o i) ∈ (xs.drop S_a).take (S_a1 - S_a) := by
      have hget : ((xs.drop S_a).take (S_a1 - S_a))[i - S_a]'(by omega) =
          st.remAt (probeSlot b o i) := by
        rw [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]
        congr 2
        omega
      rw [← hget]
      exact List.getElem_mem _
    have hsub : S_a1 - S_a = (bucketRun S quot rem (probeSlot b o a)).length := by omega
    rw [← hsub]
    exact hmem
  · intro hmem
    have hne : bucketRun S quot rem (probeSlot b o a) ≠ [] :=
      List.ne_nil_of_mem hmem
    have hocc_true : st.isOcc (probeSlot b o a) = true := by
      rw [hocc]
      cases h : bucketRun S quot rem (probeSlot b o a)
      · exact absurd h hne
      · rfl
    rw [← hslice] at hmem
    set xs := (List.range ℓ).map (fun s => st.remAt (probeSlot b o s))
    obtain ⟨d, hd_lt, hd_eq⟩ := List.getElem_of_mem hmem
    rw [List.length_take, List.length_drop, List.length_map, List.length_range] at hd_lt
    have hd_len : d < (bucketRun S quot rem (probeSlot b o a)).length :=
      lt_of_lt_of_le hd_lt (Nat.min_le_left _ _)
    rw [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range] at hd_eq
    set i := S_a + d
    have hi_lt : i < ℓ := by omega
    have hi_not_lt_Sa : ¬(i < S_a) := by omega
    have hi_lt_Sa1 : i < S_a1 := by omega
    have hi_gt : occBefore st o a < runsBefore st o (i + 1) := by
      have hiff := hinv.lt_runOffset_iff hocc (by omega : a ≤ ℓ) hi_lt
      omega
    have hi_le : runsBefore st o (i + 1) ≤ occBefore st o (a + 1) :=
      (hinv.lt_runOffset_iff hocc ha1 hi_lt).mp hi_lt_Sa1
    simp only [queryCluster, queryAnyPrefix, Bool.and_eq_true, List.any_eq_true, List.mem_range,
      decide_eq_true_eq]
    exact ⟨hocc_true, i, hi_lt, ⟨hi_gt, hi_le⟩, hd_eq⟩

/-- Pure membership query on `st : FilterState b f` under `hinv : FilterInv n S quot rem st`. -/
@[expose] noncomputable def FilterInv.querySlot {U b f n : ℕ} {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)} {st : FilterState b f}
    (hinv : FilterInv n S quot rem st) (hS_lt : #S < 2 ^ b) (u : Fin U) : Bool :=
  queryCluster st (hinv.clusterStart hS_lt (quot u))
    (hinv.backLen hS_lt (quot u)) (hinv.clusterLen hS_lt (quot u)) (rem u)

/-- **Exact fingerprint-collision characterization of `querySlot`**:
`hinv.querySlot hS_lt u = true ↔ ∃ x ∈ S, quot x = quot u ∧ rem x = rem u`. -/
theorem FilterInv.querySlot_eq_true_iff {U b f n : ℕ} {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)} {st : FilterState b f}
    (hinv : FilterInv n S quot rem st) (hS_lt : #S < 2 ^ b) (u : Fin U) :
    hinv.querySlot hS_lt u = true ↔ ∃ x ∈ S, quot x = quot u ∧ rem x = rem u := by
  rw [← mem_bucketRun_iff]
  set q := quot u
  set a := hinv.backLen hS_lt q
  set t := hinv.fwdLen hS_lt q
  set o := hinv.clusterStart hS_lt q
  set ℓ := hinv.clusterLen hS_lt q
  have hq_eq : probeSlot b o a = q := by
    dsimp only [o, clusterStart]
    simpa using probeSlot_backSlot_add q a 0
  by_cases ht_pos : 1 ≤ t
  · have ha_lt_ℓ : a < ℓ := by dsimp only [ℓ, clusterLen]; omega
    have hvalid := hinv.intervalValid_cluster hS_lt q
    rw [FilterInv.querySlot, hvalid.queryCluster_eq_true_iff hinv.isOcc_eq ha_lt_ℓ, hq_eq]
  · have ht0 : t = 0 := by omega
    have hfull_q : st.isFull q = false := by
      have h1 := hinv.isFull_probeSlot_fwdLen hS_lt q
      change st.isFull (probeSlot b q t) = false at h1
      rw [ht0, probeSlot_zero] at h1
      exact h1
    have hocc_q : st.isOcc q = false := (hinv.empty_slot q hfull_q).1
    have hrun_nil : bucketRun S quot rem q = [] := by
      have h1 := hinv.isOcc_eq q
      rw [hocc_q] at h1
      cases h : bucketRun S quot rem q
      · rfl
      · simp [h] at h1
    have hqs : hinv.querySlot hS_lt u = false := by
      dsimp only [FilterInv.querySlot, queryCluster]
      change (st.isOcc (probeSlot b o a) && _) = false
      rw [hq_eq, hocc_q]
      rfl
    simp [hqs, hrun_nil]

/-- **Pathwise zero false negatives**: if `u ∈ S`, `hinv.querySlot hS_lt u = true`. -/
theorem FilterInv.querySlot_of_mem {U b f n : ℕ} {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)} {st : FilterState b f}
    (hinv : FilterInv n S quot rem st) (hS_lt : #S < 2 ^ b) {u : Fin U} (hu : u ∈ S) :
    hinv.querySlot hS_lt u = true :=
  (hinv.querySlot_eq_true_iff hS_lt u).mpr ⟨u, hu, rfl, rfl⟩

end Cslib.DataStructure.ApproximateMembership.QuotientFilter
