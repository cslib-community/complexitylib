/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.QueryCount

/-!
# The Fredman–Komlós–Szemerédi two-level table

The static dictionary of Fredman, Komlós and Szemerédi [FredmanKomlosSzemeredi1984] stores a set
of `n` keys so that membership is decided by a constant number of memory probes, in `O(n)` cells.
This file follows the account of [CLRS2009], Section 11.5. A top-level hash `h₀` into `n` values
sorts the keys into buckets `B j = {x | h₀ x = j}`; bucket `j` gets its own block of `b_j²` cells,
where `b_j = |B j|`, and a secondary hash `g_j` into `b_j²` values that is injective on `B j`. A key
`x` is stored at cell `offset (h₀ x) + g_{h₀ x} x`.

## The model

Hash functions come from a range-indexed family `PerfectHashing.Family`: for each `r`, seeds of
type `Seed r` describe functions `X → Fin (r + 1)`. A `PerfectHashing.Description` chooses a top
member and one secondary member per bucket. The table occupies the cells `0, 1, 2, …` of a memory
of typed cells (`PerfectHashing.Cell`):

* cell `0` holds the top member;
* cell `1 + j` holds the header of bucket `j`: `empty` for an empty bucket, otherwise the address of
  its block together with its secondary member;
* the blocks follow, one after the other, and slot `offset j + g_j x` holds the key `x`.

A cell holds one key, one seed, or one address with one seed. On a word RAM a seed of a family such
as `(a x + b) mod p mod m` occupies `O(1)` words, but this file counts typed cells, not words or
bits. The bound of `5 n + 2` cells is therefore `O(n)` words only for families whose seeds fit in
`O(1)` words; such a family is not formalized here, and a seed of the uniformly random function
family used in the tests is a whole function table. Likewise the `3` probes of a lookup count
memory reads only: evaluating the hash functions is not charged.

`PerfectHashing.lookup F x` is an `OracleComp` over the memory interface (`PerfectHashing.memSpec`,
the read of one cell per call). The algorithm depends only on the family and the key; the table is
the memory it reads. It reads the top cell, then the header of `h₀ x`, then the slot of `x`, and
compares the stored key with `x`.

## Main definitions

* `PerfectHashing.Family`, `PerfectHashing.Member`: range-indexed hash families and their members.
* `PerfectHashing.Description`, `PerfectHashing.bucket`, `PerfectHashing.width`,
  `PerfectHashing.offset`, `PerfectHashing.slot`, `PerfectHashing.size`: the description of a
  table and its layout.
* `PerfectHashing.Cell`, `PerfectHashing.memory`: the cells of the table for a key list.
* `PerfectHashing.lookup`, `PerfectHashing.runLookup`: membership as a probe program, and its run
  on a memory.
* `PerfectHashing.SecondaryInjective`, `PerfectHashing.Valid`: injective secondary hashes, and the
  full FKS conditions (`n` buckets, `∑ b_j² ≤ 4n`, blocks of `b_j²` cells).

## Main results

* `PerfectHashing.runLookup_memory`: **correctness**, `lookup x` answers `x ∈ keys` whenever the
  secondary hashes are injective on their buckets.
* `PerfectHashing.isQueryBounded_lookup`: **worst-case probes**, every lookup reads at most `3`
  cells, whatever the memory.
* `PerfectHashing.size_eq`, `PerfectHashing.size_le`: **space**, a valid table occupies exactly
  `n + 1 + ∑ b_j²` cells for `n ≥ 1`, at most `5 n + 2`, and
  `PerfectHashing.memory_of_size_le` says every later cell is empty.

## References

* [M. L. Fredman, J. Komlós, E. Szemerédi, *Storing a Sparse Table with O(1) Worst Case Access
  Time*][FredmanKomlosSzemeredi1984]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, C. Stein, *Introduction to Algorithms*, 3rd ed.,
  Section 11.5][CLRS2009]
-/

@[expose] public section

namespace Cslib.DataStructure.Dictionary.PerfectHashing

open Finset

/-- A range-indexed hash family on `X`: for each `r`, seeds of type `Seed r`, drawn from the law
`seed r`, describe functions `hash r s : X → Fin (r + 1)`. -/
structure Family (X : Type) where
  /-- The seeds of the functions into `Fin (r + 1)`. -/
  Seed : ℕ → Type
  /-- The law of a fresh seed for range `r`. -/
  seed : (r : ℕ) → PMF (Seed r)
  /-- The function described by a seed. -/
  hash : (r : ℕ) → Seed r → X → Fin (r + 1)

variable {X : Type}

/-- A member of a family: a range `r` with a seed of the functions into `Fin (r + 1)`. -/
structure Member (F : Family X) where
  /-- The functions take values in `Fin (range + 1)`. -/
  range : ℕ
  /-- The seed. -/
  seed : F.Seed range

/-- The function described by a member. -/
def Member.apply {F : Family X} (g : Member F) (x : X) : Fin (g.range + 1) :=
  F.hash g.range g.seed x

/-- A two-level table: a top member and, for each of its values, a secondary member. -/
structure Description (F : Family X) where
  /-- The top-level hash, whose values index the buckets. -/
  top : Member F
  /-- The secondary hash of each bucket. -/
  secondary : Fin (top.range + 1) → Member F

/-- One typed memory cell of the table. -/
inductive Cell (F : Family X) where
  /-- The top-level member, stored in cell `0`. -/
  | top (g : Member F)
  /-- The header of a nonempty bucket: the first address of its block and its secondary member. -/
  | bucket (offset : ℕ) (g : Member F)
  /-- A stored key. -/
  | key (x : X)
  /-- An unused cell. -/
  | empty

/-- The memory interface: a call `a` reads cell `a`. -/
abbrev memSpec (F : Family X) : OracleSpec ℕ := fun _ => Cell F

section Layout

variable {F : Family X} [DecidableEq X]

/-- The keys of the list that the top-level hash sends to `j`. -/
def bucket (D : Description F) (keys : List X) (j : Fin (D.top.range + 1)) : Finset X :=
  keys.toFinset.filter fun x => D.top.apply x = j

/-- The number of cells of the block of bucket `j`: `0` for an empty bucket, otherwise the number
of values of its secondary hash. -/
def width (D : Description F) (keys : List X) (j : Fin (D.top.range + 1)) : ℕ :=
  if (bucket D keys j).card = 0 then 0 else (D.secondary j).range + 1

/-- The first address of the block of bucket `j`, after the top cell, the headers and the earlier
blocks. -/
def offset (D : Description F) (keys : List X) (j : Fin (D.top.range + 1)) : ℕ :=
  D.top.range + 2 + ∑ i ∈ Iio j, width D keys i

/-- The number of cells used by the table: the top cell, the headers and the blocks. -/
def size (D : Description F) (keys : List X) : ℕ :=
  D.top.range + 2 + ∑ j, width D keys j

/-- The cell assigned to a key: its slot in the block of its bucket. -/
def slot (D : Description F) (keys : List X) (x : X) : ℕ :=
  offset D keys (D.top.apply x) + (D.secondary (D.top.apply x)).apply x

/-- The cells of the table for the key list `keys`. -/
def memory (D : Description F) (keys : List X) (a : ℕ) : Cell F :=
  if a = 0 then .top D.top
  else if h : a ≤ D.top.range + 1 then
    let j : Fin (D.top.range + 1) := ⟨a - 1, by omega⟩
    if (bucket D keys j).card = 0 then .empty else .bucket (offset D keys j) (D.secondary j)
  else
    match keys.find? fun x => slot D keys x = a with
    | some x => .key x
    | none => .empty

/-- Each nonempty bucket's secondary hash is injective on the bucket, so its keys get distinct
slots. -/
def SecondaryInjective (D : Description F) (keys : List X) : Prop :=
  ∀ j, Set.InjOn (D.secondary j).apply (bucket D keys j)

/-- The conditions of the FKS scheme: `n` buckets for `n ≥ 1` keys, total squared bucket size at
most `4 n`, blocks of `b_j²` cells, and injective secondary hashes. -/
structure Valid (D : Description F) (keys : List X) : Prop where
  /-- One bucket per key (one bucket when there is no key). -/
  top_range : D.top.range = keys.length - 1
  /-- The squared bucket sizes sum to at most `4 n`. -/
  sum_sq_le : ∑ j, (bucket D keys j).card ^ 2 ≤ 4 * keys.length
  /-- A nonempty bucket of `b` keys has a block of `b²` cells. -/
  secondary_range : ∀ j, (bucket D keys j).card ≠ 0 →
    (D.secondary j).range + 1 = (bucket D keys j).card ^ 2
  /-- The secondary hashes are injective on their buckets. -/
  secondaryInjective : SecondaryInjective D keys

end Layout

/-- **Membership query** of the FKS table over the memory interface: read the top member `h₀` in
cell `0`, the header of bucket `h₀ x` in cell `1 + h₀ x`, and, if the bucket is nonempty, the slot
`offset + g x` given by its header, and compare the stored key with `x`. -/
def lookup (F : Family X) [DecidableEq X] (x : X) : OracleComp (memSpec F) Bool :=
  OracleComp.query (spec := memSpec F) 0 >>= fun c₀ =>
    match c₀ with
    | .top h₀ =>
      OracleComp.query (spec := memSpec F) (1 + (h₀.apply x : ℕ)) >>= fun c₁ =>
        match c₁ with
        | .bucket off g =>
          OracleComp.query (spec := memSpec F) (off + (g.apply x : ℕ)) >>= fun c₂ =>
            match c₂ with
            | .key y => pure (decide (y = x))
            | _ => pure false
        | _ => pure false
    | _ => pure false

/-- Run a membership query on a memory. -/
def runLookup (F : Family X) [DecidableEq X] (mem : ℕ → Cell F) (x : X) : Bool :=
  OracleComp.interpret (m := Id) (fun a => pure (mem a)) (lookup F x)

section Correctness

variable {F : Family X} [DecidableEq X]

theorem mem_bucket {D : Description F} {keys : List X} {j : Fin (D.top.range + 1)} {x : X} :
    x ∈ bucket D keys j ↔ x ∈ keys ∧ D.top.apply x = j := by
  simp [bucket]

theorem memory_zero (D : Description F) (keys : List X) : memory D keys 0 = .top D.top := rfl

/-- The header cell of bucket `j`. -/
theorem memory_header (D : Description F) (keys : List X) (j : Fin (D.top.range + 1)) :
    memory D keys (1 + (j : ℕ)) =
      if (bucket D keys j).card = 0 then .empty else .bucket (offset D keys j) (D.secondary j) := by
  have hj := j.isLt
  rw [memory, ite_eq_right (by omega), dite_eq_left (by omega)]
  have hj' : (⟨1 + (j : ℕ) - 1, by omega⟩ : Fin (D.top.range + 1)) = j := Fin.ext (by simp)
  rw [hj']

/-- A block cell holds the key whose slot it is, if any. -/
theorem memory_of_lt {D : Description F} {keys : List X} {a : ℕ} (ha : D.top.range + 1 < a) :
    memory D keys a = match keys.find? fun x => slot D keys x = a with
      | some x => .key x
      | none => .empty := by
  rw [memory, ite_eq_right (by omega), dite_eq_right (by omega)]

/-- Blocks of different buckets do not overlap: the block of `i` ends before that of a later `j`
starts. -/
theorem offset_add_width_le {D : Description F} {keys : List X} {i j : Fin (D.top.range + 1)}
    (hij : i < j) : offset D keys i + width D keys i ≤ offset D keys j := by
  simp only [offset, add_assoc]
  gcongr
  rw [add_comm (∑ k ∈ Iio i, width D keys k), ← sum_insert (s := Iio i) (a := i) (by simp)]
  exact sum_le_sum_of_subset fun k hk => by
    simp only [mem_insert, mem_Iio] at hk ⊢
    rcases hk with rfl | hk
    · exact hij
    · exact hk.trans hij

/-- A stored key's slot lies in the block of its bucket. -/
theorem slot_lt_offset_add_width {D : Description F} {keys : List X} {x : X} (hx : x ∈ keys) :
    slot D keys x < offset D keys (D.top.apply x) + width D keys (D.top.apply x) := by
  have hne : (bucket D keys (D.top.apply x)).card ≠ 0 :=
    card_ne_zero.mpr ⟨x, mem_bucket.mpr ⟨hx, rfl⟩⟩
  rw [slot, width, ite_eq_right hne]
  have := ((D.secondary (D.top.apply x)).apply x).isLt
  omega

/-- The slots of the keys are distinct. -/
theorem slot_injOn {D : Description F} {keys : List X} (hD : SecondaryInjective D keys) :
    Set.InjOn (slot D keys) {x | x ∈ keys} := by
  intro x hx y hy hxy
  rcases lt_trichotomy (D.top.apply x) (D.top.apply y) with hlt | heq | hgt
  · have h₁ := slot_lt_offset_add_width (D := D) hx
    have h₂ := offset_add_width_le (D := D) (keys := keys) hlt
    have h₃ : offset D keys (D.top.apply y) ≤ slot D keys y := Nat.le_add_right _ _
    omega
  · have hy' : y ∈ bucket D keys (D.top.apply x) := mem_bucket.mpr ⟨hy, heq.symm⟩
    refine hD (D.top.apply x) (mem_bucket.mpr ⟨hx, rfl⟩) hy' (Fin.ext ?_)
    have hxy' := hxy
    simp only [slot] at hxy'
    rw [← heq] at hxy'
    omega
  · have h₁ := slot_lt_offset_add_width (D := D) hy
    have h₂ := offset_add_width_le (D := D) (keys := keys) hgt
    have h₃ : offset D keys (D.top.apply x) ≤ slot D keys x := Nat.le_add_right _ _
    omega

/-- The slot of a stored key holds that key. -/
theorem memory_slot {D : Description F} {keys : List X} (hD : SecondaryInjective D keys) {x : X}
    (hx : x ∈ keys) : memory D keys (slot D keys x) = .key x := by
  have hgt : D.top.range + 1 < slot D keys x := by
    have := Nat.le_add_right (offset D keys (D.top.apply x))
      ((D.secondary (D.top.apply x)).apply x : ℕ)
    simp only [offset] at this
    simp only [slot, offset]
    omega
  rw [memory_of_lt hgt]
  obtain ⟨y, hy⟩ : ∃ y, keys.find? (fun z => slot D keys z = slot D keys x) = some y :=
    Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨x, hx, by simp⟩)
  have hyx : y = x := slot_injOn hD (List.mem_of_find?_eq_some hy) hx
    (by simpa using List.find?_some hy)
  rw [hy, hyx]

/-- Every key cell holds a key of the list. -/
theorem mem_of_memory_eq_key {D : Description F} {keys : List X} {a : ℕ} {y : X}
    (h : memory D keys a = .key y) : y ∈ keys := by
  by_cases ha : D.top.range + 1 < a
  · rw [memory_of_lt ha] at h
    cases hf : keys.find? (fun x => slot D keys x = a) with
    | none => rw [hf] at h; cases h
    | some z =>
      rw [hf] at h
      cases h
      exact List.mem_of_find?_eq_some hf
  · rw [memory] at h
    by_cases h0 : a = 0
    · rw [ite_eq_left h0] at h
      cases h
    · rw [ite_eq_right h0, dite_eq_left (by omega)] at h
      dsimp only at h
      split_ifs at h

/-- A lookup run on a memory is the case analysis on the cells it reads. -/
theorem runLookup_eq (mem : ℕ → Cell F) (x : X) :
    runLookup F mem x =
      match mem 0 with
      | .top h₀ =>
        match mem (1 + (h₀.apply x : ℕ)) with
        | .bucket off g =>
          match mem (off + (g.apply x : ℕ)) with
          | .key y => decide (y = x)
          | _ => false
        | _ => false
      | _ => false := by
  simp only [runLookup, lookup, OracleComp.interpret_bind, OracleComp.interpret_query, pure_bind]
  rcases mem 0 with h₀ | _ | _ | _
  · simp only [OracleComp.interpret_bind, OracleComp.interpret_query, pure_bind]
    rcases mem (1 + (h₀.apply x : ℕ)) with _ | ⟨off, g⟩ | _ | _
    · rfl
    · simp only [OracleComp.interpret_bind, OracleComp.interpret_query, pure_bind]
      rcases mem (off + (g.apply x : ℕ)) with _ | _ | y | _ <;> rfl
    · rfl
    · rfl
  all_goals rfl

/-- **Correctness of the FKS lookup.** If the secondary hashes are injective on their buckets, the
lookup of `x` in the table of `keys` answers whether `x` is a key. -/
theorem runLookup_memory {D : Description F} {keys : List X} (hD : SecondaryInjective D keys)
    (x : X) : runLookup F (memory D keys) x = decide (x ∈ keys) := by
  rw [runLookup_eq, memory_zero]
  dsimp only
  rw [memory_header]
  by_cases hx : x ∈ keys
  · have hne : (bucket D keys (D.top.apply x)).card ≠ 0 :=
      card_ne_zero.mpr ⟨x, mem_bucket.mpr ⟨hx, rfl⟩⟩
    rw [ite_eq_right hne]
    dsimp only
    rw [show offset D keys (D.top.apply x) + ((D.secondary (D.top.apply x)).apply x : ℕ) =
      slot D keys x from rfl, memory_slot hD hx]
    simp [hx]
  · by_cases hempty : (bucket D keys (D.top.apply x)).card = 0
    · rw [ite_eq_left hempty]
      simp [hx]
    · rw [ite_eq_right hempty]
      dsimp only
      generalize hc : memory D keys (offset D keys (D.top.apply x) +
        ((D.secondary (D.top.apply x)).apply x : ℕ)) = c
      cases c with
      | key y =>
        have hy := mem_of_memory_eq_key hc
        have hyx : y ≠ x := fun h => hx (h ▸ hy)
        simp [hx, hyx]
      | top g => simp [hx]
      | bucket off g => simp [hx]
      | empty => simp [hx]

end Correctness

/-- **Worst-case probes.** A lookup reads at most three cells, whatever the memory holds. -/
theorem isQueryBounded_lookup (F : Family X) [DecidableEq X] (x : X) :
    OracleComp.IsQueryBounded (lookup F x) 3 := by
  refine OracleComp.IsCostBounded.bind (n := 1) (m := 2) (OracleComp.IsCostBounded.query _)
    fun c₀ => ?_
  rcases c₀ with h₀ | _ | _ | _
  · refine OracleComp.IsCostBounded.bind (n := 1) (m := 1) (OracleComp.IsCostBounded.query _)
      fun c₁ => ?_
    rcases c₁ with _ | ⟨off, g⟩ | _ | _
    · exact .pure _ _
    · refine (OracleComp.IsCostBounded.bind (n := 1) (m := 0) (OracleComp.IsCostBounded.query _)
        fun c₂ => ?_)
      rcases c₂ with _ | _ | y | _ <;> exact .pure _ _
    · exact .pure _ _
    · exact .pure _ _
  all_goals exact .pure _ _

section Space

variable {F : Family X} [DecidableEq X]

/-- Every key's slot lies inside the table. -/
theorem slot_lt_size {D : Description F} {keys : List X} {x : X} (hx : x ∈ keys) :
    slot D keys x < size D keys := by
  refine (slot_lt_offset_add_width hx).trans_le ?_
  simp only [offset, size, add_assoc]
  gcongr
  rw [add_comm (∑ k ∈ Iio (D.top.apply x), width D keys k),
    ← sum_insert (s := Iio (D.top.apply x)) (a := D.top.apply x) (by simp)]
  exact sum_le_sum_of_subset fun _ _ => mem_univ _

/-- The table uses no cell at or beyond `size`. -/
theorem memory_of_size_le {D : Description F} {keys : List X} {a : ℕ} (ha : size D keys ≤ a) :
    memory D keys a = .empty := by
  have hgt : D.top.range + 1 < a := by
    simp only [size] at ha
    omega
  rw [memory_of_lt hgt, List.find?_eq_none.mpr]
  intro x hx
  have := slot_lt_size (D := D) hx
  simp only [decide_eq_true_eq]
  omega

/-- **Exact space.** With blocks of `b_j²` cells, the table occupies the top cell, one header per
bucket and `∑ b_j²` block cells. -/
theorem size_eq {D : Description F} {keys : List X}
    (h : ∀ j, (bucket D keys j).card ≠ 0 →
      (D.secondary j).range + 1 = (bucket D keys j).card ^ 2) :
    size D keys = D.top.range + 2 + ∑ j, (bucket D keys j).card ^ 2 := by
  simp only [size]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  rw [width]
  split_ifs with hj
  · simp [hj]
  · exact h j hj

/-- **Linear space.** A valid table for `n` keys occupies at most `5 n + 2` cells. -/
theorem size_le {D : Description F} {keys : List X} (hD : Valid D keys) :
    size D keys ≤ 5 * keys.length + 2 := by
  rw [size_eq hD.secondary_range]
  have h₁ := hD.top_range
  have h₂ := hD.sum_sq_le
  omega

end Space

end Cslib.DataStructure.Dictionary.PerfectHashing
