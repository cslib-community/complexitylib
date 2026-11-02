/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.CuckooHashing.Model
public import Complexity.DataStructure.HashFamily.Memory
public import Complexity.DataStructure.StateTransition.WP

/-!
# Cuckoo hashing over the memory oracle: layout and lookup

This file lays out a cuckoo hash table in named field arrays over `Memory.spec w` and implements
its lookup. The seed of `Scheme` is a pair of random tables `Fin U → Fin (2 ^ b)` stored in two
fields, as in the memory pilot `HashFamily.RandomTable`, and the scheme is
`Memory.scheme U b maxLoop attempts`.

The storage (`Layout`) is one contiguous region: a count, a freshness flag, the keys and the
values in insertion order (`keys`, `vals`, capacity `n_max`), the two tables `t1`, `t2` of
`2 ^ b` slots each, and the two hash tables `h1`, `h2` of `U` cells each. A slot holds `0` when
empty and `i + 1` for the entry of insertion index `i` (`slotWord`), so a probe reads the slot and
then the key it points to.

The abstraction function (`Layout.abs`) reads the seed from the hash tables, the keys, values and
count from the records, and the flag, as a `Model`. The tables do not appear in the abstraction:
the invariant (`Layout.Inv`) asks that they encode the replay of the keys under the seed
(`Layout.Encodes`). This is the only place where the pure table model of
`WordRAM.CuckooHashing` meets memory.

Memory programs are specified by weakest preconditions with cost
(`StateTransitionSpec.wp`). A lookup probes `t1` at `h1 u`, then `t2` at `h2 u` (`Layout.probe`).
Under the invariant it computes `lookupEntry` on the replayed tables (`Layout.wp_probe`), hence
the insertion index of `u` when `u` is stored (`Layout.lookupEntry_map_idx`). It reads at most six
cells, and seven with the value (`Layout.wp_getProg`).

## Main definitions

* `Memory.Seed`, `Memory.scheme`: random hash tables, and the cuckoo scheme over them with the
  position map as fallback.
* `Memory.Layout`: the fields, with `Layout.span` cells in all.
* `Memory.slotWord`: the word stored in a slot.
* `Memory.Layout.abs`: the model state stored in memory.
* `Memory.Layout.Encodes`, `Memory.Layout.Records`, `Memory.Layout.Inv`: the tables, the
  records, and the implementation invariant.
* `Memory.Layout.InTables`, `Memory.Layout.SameKeys`: frames.
* `Memory.Layout.probe`, `Memory.Layout.getProg`: lookup.

## Main results

* `Memory.Layout.abs_congr`, `Memory.Layout.Records.congr`: the abstraction and the records
  depend only on the cells outside the tables.
* `Memory.Layout.wp_probe`, `Memory.Layout.lookupEntry_map_idx`: a probe answers `lookupEntry`,
  the insertion index of a stored key.
* `Memory.Layout.wp_getProg`: a lookup answers the stored dictionary in seven reads.
* `Memory.Layout.exists_run_liftRight_of_wp`: a deterministic program run with coins.

## References

* [R. Pagh and F. F. Rodler, "Cuckoo hashing"][PaghRodler2004]
-/

@[expose] public section

namespace Cslib.DataStructure.Dictionary.CuckooHashing.Memory

open Cslib.WordRAM Cslib.DataStructure
open Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing
open Cslib.DataStructure.HashFamily.RandomTable (tableOf)

/-! ## The scheme -/

/-- A seed: the two hash tables. -/
abbrev Seed (U b : ℕ) : Type := (Fin U → Fin (2 ^ b)) × (Fin U → Fin (2 ^ b))

/-- The position of `u` in `ks` if it occurs, and `0` otherwise. -/
def posMap {U : ℕ} (ks : List (Fin U)) (u : Fin U) : ℕ :=
  if u ∈ ks then ks.idxOf u else 0

/-- Cuckoo hashing with random hash tables. The fallback seed hashes the keys to their
positions in the first table, and everything else to slot `0`. -/
def scheme (U b maxLoop attempts : ℕ) : Scheme (Seed U b) U (2 ^ b) where
  hash₁ := Prod.fst
  hash₂ := Prod.snd
  maxLoop := maxLoop
  attempts := attempts
  fallback ks := (fun u => Fin.ofNat _ (posMap ks u), fun _ => 0)

/-- The word stored in a slot: `0` when empty, and the insertion index plus one otherwise. -/
def slotWord {U : ℕ} : Option (SlotEntry U) → ℕ
  | none => 0
  | some e => e.idx + 1

@[simp] theorem slotWord_none {U : ℕ} : slotWord (none : Option (SlotEntry U)) = 0 := rfl

@[simp] theorem slotWord_some {U : ℕ} (e : SlotEntry U) : slotWord (some e) = e.idx + 1 := rfl

/-! ## The layout -/

/-- A cuckoo hash table for keys `Fin U`, tables of `2 ^ b` slots and at most `n_max` keys,
stored from address `base`. -/
structure Layout (U b n_max : ℕ) where
  /-- The first address. -/
  base : ℕ

namespace Layout

variable {U b n_max : ℕ} (L : Layout U b n_max)

/-- The number of stored keys. -/
def count : Block := ⟨L.base, 1⟩

/-- Whether the seed was drawn fresh: nonzero if so. -/
def fresh : Block := ⟨L.base + 1, 1⟩

/-- The keys in insertion order. -/
def keys : Block := ⟨L.base + 2, n_max⟩

/-- The values in insertion order. -/
def vals : Block := ⟨L.base + 2 + n_max, n_max⟩

/-- The first table. -/
def t1 : Block := ⟨L.base + 2 + 2 * n_max, 2 ^ b⟩

/-- The second table. -/
def t2 : Block := ⟨L.base + 2 + 2 * n_max + 2 ^ b, 2 ^ b⟩

/-- The first hash table. -/
def h1 : Block := ⟨L.base + 2 + 2 * n_max + 2 * 2 ^ b, U⟩

/-- The second hash table. -/
def h2 : Block := ⟨L.base + 2 + 2 * n_max + 2 * 2 ^ b + U, U⟩

variable (U b n_max) in
/-- The number of cells of the layout. -/
def span : ℕ := 2 + 2 * n_max + 2 * 2 ^ b + 2 * U

@[simp] theorem count_base : L.count.base = L.base := rfl
@[simp] theorem fresh_base : L.fresh.base = L.base + 1 := rfl
@[simp] theorem keys_base : L.keys.base = L.base + 2 := rfl
@[simp] theorem vals_base : L.vals.base = L.base + 2 + n_max := rfl
@[simp] theorem t1_base : L.t1.base = L.base + 2 + 2 * n_max := rfl
@[simp] theorem t2_base : L.t2.base = L.base + 2 + 2 * n_max + 2 ^ b := rfl
@[simp] theorem h1_base : L.h1.base = L.base + 2 + 2 * n_max + 2 * 2 ^ b := rfl
@[simp] theorem h2_base : L.h2.base = L.base + 2 + 2 * n_max + 2 * 2 ^ b + U := rfl
@[simp] theorem count_length : L.count.length = 1 := rfl
@[simp] theorem fresh_length : L.fresh.length = 1 := rfl
@[simp] theorem keys_length : L.keys.length = n_max := rfl
@[simp] theorem vals_length : L.vals.length = n_max := rfl
@[simp] theorem t1_length : L.t1.length = 2 ^ b := rfl
@[simp] theorem t2_length : L.t2.length = 2 ^ b := rfl
@[simp] theorem h1_length : L.h1.length = U := rfl
@[simp] theorem h2_length : L.h2.length = U := rfl

/-! ## The stored model -/

/-- The stored number of keys. -/
def n (s : Memory.State) : ℕ := s.mem L.base

/-- The stored keys in insertion order. -/
def keyList [NeZero U] (s : Memory.State) : List (Fin U) :=
  (L.keys.entries (L.n s) s.mem).map (Fin.ofNat U)

/-- The stored values in insertion order. -/
def valList (s : Memory.State) : List ℕ := L.vals.entries (L.n s) s.mem

/-- The stored seed: the two hash tables. -/
def seed (s : Memory.State) : Seed U b := (tableOf L.h1 b U s, tableOf L.h2 b U s)

/-- The value of a key in insertion-ordered keys and values. -/
def dictOf {U : ℕ} (ks : List (Fin U)) (vs : List ℕ) : Dictionary.State U :=
  fun u => vs[ks.idxOf u]?

/-- The model state stored in memory. -/
def abs [NeZero U] (s : Memory.State) : Model (Seed U b) U :=
  ⟨L.seed s, L.keyList s, dictOf (L.keyList s) (L.valList s), s.mem (L.base + 1) ≠ 0⟩

@[simp] theorem abs_seed [NeZero U] (s : Memory.State) : (L.abs s).seed = L.seed s := rfl
@[simp] theorem abs_keys [NeZero U] (s : Memory.State) : (L.abs s).keys = L.keyList s := rfl
@[simp] theorem abs_dict [NeZero U] (s : Memory.State) :
    (L.abs s).dict = dictOf (L.keyList s) (L.valList s) := rfl

@[simp] theorem length_keyList [NeZero U] (s : Memory.State) : (L.keyList s).length = L.n s := by
  simp [keyList]

@[simp] theorem length_valList (s : Memory.State) : (L.valList s).length = L.n s := by
  simp [valList]

/-- The addresses of the two tables. -/
def InTables (a : ℕ) : Prop := L.t1.base ≤ a ∧ a < L.t1.base + 2 * 2 ^ b

/-- The tables in memory encode `T`. -/
def Encodes (s : Memory.State) (T : PureTable U (2 ^ b)) : Prop :=
  ∀ j : Fin (2 ^ b), s.mem (L.t1.base + j) = slotWord (T.t1 j) ∧
    s.mem (L.t2.base + j) = slotWord (T.t2 j)

variable [NeZero U]

/-- The records of a cuckoo hash table: the layout is allocated, at most `n_max` keys are
stored, keys and hash values are in range, and keys are distinct. -/
structure Records (s : Memory.State) : Prop where
  /-- Every field is allocated. -/
  allocated : L.base + span U b n_max ≤ s.frontier
  /-- At most `n_max` keys are stored. -/
  count_le : L.n s ≤ n_max
  /-- Every stored key is below `U`. -/
  keys_lt : ∀ i < L.n s, s.mem (L.keys.base + i) < U
  /-- The stored keys are distinct. -/
  nodup : (L.keyList s).Nodup
  /-- The first hash table holds slot indices. -/
  h1_lt : ∀ u < U, s.mem (L.h1.base + u) < 2 ^ b
  /-- The second hash table holds slot indices. -/
  h2_lt : ∀ u < U, s.mem (L.h2.base + u) < 2 ^ b

/-- The implementation invariant at eviction cap `maxLoop`: the records, and tables that encode
the replay of the keys under the seed. -/
structure Inv (maxLoop : ℕ) (s : Memory.State) : Prop extends L.Records s where
  /-- The tables encode the replay of the keys. -/
  tables : ∃ T, pureReplay (L.seed s).1 (L.seed s).2 maxLoop (L.keyList s) = some T ∧
    L.Encodes s T

variable {L} {maxLoop : ℕ}

/-! ## Frames -/

omit [NeZero U] in
/-- Two memories agree on the count, the stored keys and the hash tables. -/
structure SameKeys (s s' : Memory.State) : Prop where
  /-- The same count. -/
  n_eq : L.n s' = L.n s
  /-- The same keys. -/
  keys_eq : ∀ i < L.n s, s'.mem (L.keys.base + i) = s.mem (L.keys.base + i)
  /-- The same first hash table. -/
  h1_eq : ∀ u < U, s'.mem (L.h1.base + u) = s.mem (L.h1.base + u)
  /-- The same second hash table. -/
  h2_eq : ∀ u < U, s'.mem (L.h2.base + u) = s.mem (L.h2.base + u)

omit [NeZero U] in
/-- Memories that agree outside the tables agree on the count, the keys and the hash tables. -/
theorem SameKeys.of_frame {s s' : Memory.State} (hn : L.n s ≤ n_max)
    (h : ∀ a, ¬ L.InTables a → s'.mem a = s.mem a) : L.SameKeys s s' where
  n_eq := h _ (by simp only [InTables, t1_base]; omega)
  keys_eq i hi := h _ (by simp only [InTables, t1_base, keys_base]; omega)
  h1_eq u hu := h _ (by simp only [InTables, t1_base, h1_base]; omega)
  h2_eq u hu := h _ (by simp only [InTables, t1_base, h2_base]; omega)

omit [NeZero U] in
theorem SameKeys.seed_eq {s s' : Memory.State} (h : L.SameKeys s s') : L.seed s' = L.seed s := by
  simp only [seed]
  congr 1 <;> funext u <;> unfold tableOf
  · rw [h.h1_eq u u.2]
  · rw [h.h2_eq u u.2]

/-- The stored keys depend only on the count and the key cells. -/
theorem keyList_congr {s s' : Memory.State} (hn : L.n s' = L.n s)
    (hk : ∀ i < L.n s, s'.mem (L.keys.base + i) = s.mem (L.keys.base + i)) :
    L.keyList s' = L.keyList s := by
  simp only [keyList, hn]
  rw [Block.entries_congr _ _ hk]

omit [NeZero U] in
/-- The stored values depend only on the count and the value cells. -/
theorem valList_congr {s s' : Memory.State} (hn : L.n s' = L.n s)
    (hv : ∀ i < L.n s, s'.mem (L.vals.base + i) = s.mem (L.vals.base + i)) :
    L.valList s' = L.valList s := by
  simp only [valList, hn]
  rw [Block.entries_congr _ _ hv]

theorem SameKeys.keyList_eq {s s' : Memory.State} (h : L.SameKeys s s') :
    L.keyList s' = L.keyList s :=
  keyList_congr h.n_eq h.keys_eq

/-- The stored model depends only on the cells outside the tables. -/
theorem abs_congr {s s' : Memory.State} (hn : L.n s ≤ n_max)
    (h : ∀ a, ¬ L.InTables a → s'.mem a = s.mem a) : L.abs s' = L.abs s := by
  have hk := SameKeys.of_frame hn h
  have hv : L.valList s' = L.valList s := by
    simp only [valList, hk.n_eq]
    rw [Block.entries_congr _ _ fun i hi =>
      h _ (by simp only [InTables, t1_base, vals_base]; omega)]
  have hf : s'.mem (L.base + 1) = s.mem (L.base + 1) :=
    h _ (by simp only [InTables, t1_base]; omega)
  simp only [abs, hk.keyList_eq, hv, hk.seed_eq, hf]

/-- The records depend only on the count, the keys and the hash tables, and survive a growing
frontier. -/
theorem Records.congr {s s' : Memory.State} (hs : L.Records s) (h : L.SameKeys s s')
    (hf : s.frontier ≤ s'.frontier) : L.Records s' where
  allocated := hs.allocated.trans hf
  count_le := h.n_eq ▸ hs.count_le
  keys_lt i hi := by
    rw [h.n_eq] at hi
    rw [h.keys_eq i hi]
    exact hs.keys_lt i hi
  nodup := h.keyList_eq ▸ hs.nodup
  h1_lt u hu := (h.h1_eq u hu).symm ▸ hs.h1_lt u hu
  h2_lt u hu := (h.h2_eq u hu).symm ▸ hs.h2_lt u hu

/-- The first hash table read as words is the first hash function. -/
theorem Records.h1_eq {s : Memory.State} (h : L.Records s) (u : Fin U) :
    s.mem (L.h1.base + u) = ((L.seed s).1 u : ℕ) := by
  simp only [seed, tableOf, Fin.val_ofNat]
  exact (Nat.mod_eq_of_lt (h.h1_lt u u.2)).symm

/-- The second hash table read as words is the second hash function. -/
theorem Records.h2_eq {s : Memory.State} (h : L.Records s) (u : Fin U) :
    s.mem (L.h2.base + u) = ((L.seed s).2 u : ℕ) := by
  simp only [seed, tableOf, Fin.val_ofNat]
  exact (Nat.mod_eq_of_lt (h.h2_lt u u.2)).symm

/-- The key cells hold the stored keys. -/
theorem Records.keys_eq {s : Memory.State} (h : L.Records s) {i : ℕ}
    (hi : i < (L.keyList s).length) : s.mem (L.keys.base + i) = ((L.keyList s)[i] : ℕ) := by
  rw [length_keyList] at hi
  simp only [keyList, List.getElem_map, Block.getElem_entries, Fin.val_ofNat]
  exact (Nat.mod_eq_of_lt (h.keys_lt i hi)).symm

omit [NeZero U] in
/-- A replayed entry is stored at its insertion index. -/
theorem entry_of_replay {θ₁ θ₂ : Fin U → Fin (2 ^ b)} {ks : List (Fin U)}
    {T : PureTable U (2 ^ b)} (hnd : ks.Nodup) (hT : pureReplay θ₁ θ₂ maxLoop ks = some T)
    {e : SlotEntry U} (he : EntryIn T e) : ∃ h : e.idx < ks.length, ks[e.idx] = e.key := by
  have hmem := ((pureReplay_spec hnd hT).2 e).mp he
  rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff] at hmem
  exact hmem

/-! ## Lookup -/

variable (L)

/-- Probe the second table for the key `u`: the insertion index stored at `h2 u`, if it holds
`u`. -/
def probe₂ (u : ℕ) : Memory.Prog (Option ℕ) := do
  let j ← L.h2.get u
  let c ← L.t2.get j
  if c = 0 then pure none else do
    let k ← L.keys.get (c - 1)
    pure (if k = u then some (c - 1) else none)

/-- Probe both tables for the key `u`: its insertion index, if it is stored. -/
def probe (u : ℕ) : Memory.Prog (Option ℕ) := do
  let j ← L.h1.get u
  let c ← L.t1.get j
  if c = 0 then L.probe₂ u else do
    let k ← L.keys.get (c - 1)
    if k = u then pure (some (c - 1)) else L.probe₂ u

/-- Look up the key `u`: its value, if it is stored. -/
def getProg (u : ℕ) : Memory.Prog (Option ℕ) := do
  let r ← L.probe u
  match r with
  | none => pure none
  | some i => do
    let v ← L.vals.get i
    pure (some v)

variable {L} {w : ℕ}

/-- Every address of the layout is allocated. -/
theorem Records.lt_frontier {s : Memory.State} (h : L.Records s) {a : ℕ}
    (ha : a < L.base + span U b n_max) : a < s.frontier :=
  lt_of_lt_of_le ha h.allocated

/-- **Probing the second table.** Under the invariant, the probe reads three cells at most and
finds the entry of `u` in the second replayed table, if any. -/
theorem wp_probe₂ {s : Memory.State} (h : L.Inv maxLoop s) {T : PureTable U (2 ^ b)}
    (hT : pureReplay (L.seed s).1 (L.seed s).2 maxLoop (L.keyList s) = some T)
    (hE : L.Encodes s T) (u : Fin U) :
    (Memory.spec w).wp Memory.charge (L.probe₂ u) (fun r s' t =>
      r = (match T.t2 ((L.seed s).2 u) with
        | some e => if e.key = u then some e.idx else none
        | none => none) ∧ s' = s ∧ t ≤ 3) s := by
  have hj := ((L.seed s).2 u).2
  have hu := u.2
  have h₁ := h.lt_frontier (a := L.h2.base + u) (by simp only [h2_base, span]; omega)
  have h₂ := h.lt_frontier (a := L.t2.base + ((L.seed s).2 u : ℕ))
    (by simp only [t2_base, span]; omega)
  simp only [probe₂, StateTransitionSpec.wp_lift_bind, StateTransitionSpec.stepFn,
    Memory.step_read, Memory.valid_read, Memory.charge_read, h.h2_eq u, (hE _).2]
  refine ⟨h₁, h₂, ?_⟩
  cases ht : T.t2 ((L.seed s).2 u) with
  | none => simp
  | some e =>
    obtain ⟨hi, hk⟩ := entry_of_replay h.nodup hT (e := e) (Or.inr ⟨_, ht⟩)
    have hn := h.count_le
    have hi' := hi
    rw [length_keyList] at hi'
    have h₃ := h.lt_frontier (a := L.keys.base + e.idx) (by simp only [keys_base, span]; omega)
    have hkey : s.mem (L.keys.base + e.idx) = (e.key : ℕ) := by
      rw [h.keys_eq hi, hk]
    simp only [slotWord_some, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel,
      StateTransitionSpec.wp_lift_bind, StateTransitionSpec.wp_pure, StateTransitionSpec.stepFn,
      Memory.step_read, Memory.valid_read, Memory.charge_read, hkey, Fin.val_inj]
    exact ⟨h₃, trivial, trivial, by omega⟩

/-- **A probe computes `lookupEntry`.** Under the invariant, a probe of `u` reads at most six
cells and answers the insertion index of the entry that `lookupEntry` finds in the replayed
tables. -/
theorem wp_probe {s : Memory.State} (h : L.Inv maxLoop s) {T : PureTable U (2 ^ b)}
    (hT : pureReplay (L.seed s).1 (L.seed s).2 maxLoop (L.keyList s) = some T)
    (hE : L.Encodes s T) (u : Fin U) :
    (Memory.spec w).wp Memory.charge (L.probe u) (fun r s' t =>
      r = (lookupEntry (L.seed s).1 (L.seed s).2 T u).map SlotEntry.idx ∧ s' = s ∧ t ≤ 6) s := by
  have hj := ((L.seed s).1 u).2
  have hu := u.2
  have h₁ := h.lt_frontier (a := L.h1.base + u) (by simp only [h1_base, span]; omega)
  have h₂ := h.lt_frontier (a := L.t1.base + ((L.seed s).1 u : ℕ))
    (by simp only [t1_base, span]; omega)
  have hp₂ := wp_probe₂ (w := w) h hT hE u
  simp only [probe, StateTransitionSpec.wp_lift_bind, StateTransitionSpec.stepFn,
    Memory.step_read, Memory.valid_read, Memory.charge_read, h.h1_eq u, (hE _).1]
  refine ⟨h₁, h₂, ?_⟩
  cases ht : T.t1 ((L.seed s).1 u) with
  | none =>
    simp only [slotWord_none, ite_true]
    refine StateTransitionSpec.wp_mono (fun r s' t ⟨hr, hs, hc⟩ => ⟨?_, hs, by omega⟩) hp₂
    rw [hr]
    unfold lookupEntry
    rw [ht]
    cases T.t2 ((L.seed s).2 u) <;> simp
  | some e =>
    obtain ⟨hi, hk⟩ := entry_of_replay h.nodup hT (e := e) (Or.inl ⟨_, ht⟩)
    have hn := h.count_le
    have hi' := hi
    rw [length_keyList] at hi'
    have h₃ := h.lt_frontier (a := L.keys.base + e.idx) (by simp only [keys_base, span]; omega)
    have hkey : s.mem (L.keys.base + e.idx) = (e.key : ℕ) := by
      rw [h.keys_eq hi, hk]
    simp only [slotWord_some, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel,
      StateTransitionSpec.wp_lift_bind, StateTransitionSpec.stepFn,
      Memory.step_read, Memory.valid_read, Memory.charge_read, hkey, Fin.val_inj]
    refine ⟨h₃, ?_⟩
    by_cases hek : e.key = u
    · simp only [hek, ite_true, StateTransitionSpec.wp_pure]
      refine ⟨?_, trivial, by omega⟩
      unfold lookupEntry
      simp [ht, hek]
    · simp only [hek, ite_false]
      refine StateTransitionSpec.wp_mono (fun r s' t ⟨hr, hs, hc⟩ => ⟨?_, hs, by omega⟩) hp₂
      rw [hr]
      unfold lookupEntry
      rw [ht]
      cases T.t2 ((L.seed s).2 u) <;> simp [hek]

/-- Under the invariant, a probe answers the insertion index of a stored key, and `none` for a
key that is not stored. -/
theorem lookupEntry_map_idx {s : Memory.State} (h : L.Inv maxLoop s) {T : PureTable U (2 ^ b)}
    (hT : pureReplay (L.seed s).1 (L.seed s).2 maxLoop (L.keyList s) = some T) (u : Fin U) :
    (lookupEntry (L.seed s).1 (L.seed s).2 T u).map SlotEntry.idx =
      if u ∈ L.keyList s then some ((L.keyList s).idxOf u) else none := by
  split_ifs with hu
  · have hlt := List.idxOf_lt_length_of_mem hu
    have h' := pureReplay_lookupEntry_of_mem h.nodup hT hlt
    rw [List.getElem_idxOf hlt] at h'
    rw [h']
    rfl
  · rw [pureReplay_lookupEntry_of_notMem h.nodup hT hu]
    rfl

omit [NeZero U] in
/-- The stored value of a key is the value at its insertion index. -/
theorem dictOf_eq {ks : List (Fin U)} {vs : List ℕ} (hlen : vs.length = ks.length) (u : Fin U) :
    dictOf ks vs u = if h : u ∈ ks then
      some (vs[ks.idxOf u]'(hlen ▸ List.idxOf_lt_length_of_mem h)) else none := by
  unfold dictOf
  split_ifs with hu
  · exact List.getElem?_eq_getElem _
  · rw [List.getElem?_eq_none]
    rw [hlen, List.idxOf_eq_length hu]

/-- **Lookup.** Under the invariant, a lookup reads at most seven cells and answers the stored
dictionary. -/
theorem wp_getProg {s : Memory.State} (h : L.Inv maxLoop s) (u : Fin U) :
    (Memory.spec w).wp Memory.charge (L.getProg u) (fun r s' t =>
      r = (L.abs s).dict u ∧ s' = s ∧ t ≤ 7) s := by
  obtain ⟨T, hT, hE⟩ := h.tables
  rw [getProg, StateTransitionSpec.wp_bind]
  refine StateTransitionSpec.wp_mono (fun r s' t ⟨hr, hs, hc⟩ => ?_) (wp_probe (w := w) h hT hE u)
  subst hs
  rw [lookupEntry_map_idx h hT] at hr
  have hlen : (L.valList s').length = (L.keyList s').length := by simp
  rw [abs_dict, dictOf_eq hlen]
  split_ifs at hr with hu
  · subst hr
    have hi := List.idxOf_lt_length_of_mem hu
    rw [length_keyList] at hi
    have hn := h.count_le
    have hv := h.lt_frontier (a := L.vals.base + (L.keyList s').idxOf u)
      (by simp only [vals_base, span]; omega)
    simp only [StateTransitionSpec.wp_lift_bind, StateTransitionSpec.wp_pure,
      StateTransitionSpec.stepFn, Memory.step_read, Memory.valid_read, Memory.charge_read,
      dite_eq_left hu]
    refine ⟨hv, ?_, trivial, by omega⟩
    simp [valList]
  · subst hr
    simp only [StateTransitionSpec.wp_pure, dite_eq_right hu]
    exact ⟨trivial, trivial, by omega⟩

/-! ## Deterministic programs under coins -/

/-- A deterministic memory program, run with coins: its weakest precondition gives its outcome,
its admissibility and its expected cost. -/
theorem exists_run_liftRight_of_wp {α : Type} {p : Memory.Prog α} {Q : α → Memory.State → ℕ → Prop}
    {s : Memory.State} (coin : ℕ → ℕ) (h : (Memory.spec w).wp Memory.charge p Q s) :
    ∃ a s' t, Q a s' t ∧
      (Memory.spec w).toRandomized.withCoins.run (OracleComp.liftRight p) s = PMF.pure (a, s') ∧
      (Memory.spec w).toRandomized.withCoins.expectedCost
        ((Memory.spec w).toRandomized.coinCharge coin Memory.charge) (OracleComp.liftRight p) s =
          t ∧
      (Memory.spec w).toRandomized.withCoins.toSpec.DemonicValid s (OracleComp.liftRight p) := by
  rw [StateTransitionSpec.wp_iff] at h
  refine ⟨_, _, _, h.2, ?_, ?_, ?_⟩
  · rw [RandomizedSpec.withCoins_run_liftRight, StateTransitionSpec.run_toRandomized]
    rfl
  · rw [RandomizedSpec.expectedCost_liftRight, StateTransitionSpec.expectedCost_toRandomized]
  · exact RandomizedSpec.demonicValid_liftRight
      (StateTransitionSpec.toRandomized_demonicValid_of_validHistory h.1)

end Layout

end Cslib.DataStructure.Dictionary.CuckooHashing.Memory
