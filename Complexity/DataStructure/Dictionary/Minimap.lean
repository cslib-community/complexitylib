/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.DataStructure.Dictionary.Dynamic.Spec
public import Complexity.DataStructure.Dictionary.DynamicMatching
public import Complexity.DataStructure.Dictionary.Spillover
public import Complexity.Foundations.Data.BitString.Combination
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Finset.Sort
public import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Fixed-Capacity Leaf Minimap

This file formalizes the pure fixed-capacity minimap representation of Tianxiao Li, Jingxun Liang,
Huacheng Yu, and Renfei Zhou, *Dynamic Dictionary with Subconstant Wasted Bits per Key*
([LiLiangYuZhou2024, Section 3.4, Lemma 3.7 at `r = 1`, and Section 5.2];
[arXiv:2310.20536v1](https://arxiv.org/abs/2310.20536v1), PDF pp. 11–12 / printed pp. 10–11 and PDF
pp. 27–28 / printed pp. 26–27).

Given key-ID universe `Fin U'`, slot capacity `n'` (`1 ≤ n' ≤ U'`), and payload universe `Fin X`
(`1 ≤ X`), a minimap represents a map of `m ≤ n'` active keys (`m = n'` at fixed leaf capacity in
Section 5.2) by separating **metadata** (`header`) from **payload slots** (`slots`):
1. Each payload `v < X` is split via `Spillover.encode n'` (`r_sp = n'`, [Patrascu2008, Lemma 3];
   [LiLiangYuZhou2024, Lemma 3.8]) into a spillover value `k ∈ Fin K`
   (`K = Spillover.spillUniv X n' ≤ 2 * n'`) and an `M`-bit slot word `mem ∈ Fin (2 ^ M)`
   (`M = Spillover.memBits X n'`).
2. The active key set `S ⊆ Fin U'` (`S.card = m`) together with the tuple of spillover values
   `Fin m → Fin K` listed in increasing order of key in `S` is bijected computably onto a single
   metadata index `header : Fin (U'.choose m * K ^ m)` via `Cslib.BitString.subsetEquiv`,
   `finFunctionFinEquiv`, and `finProdFinEquiv`.
3. Under a dynamic matching scheme `h : DynamicMatching.Scheme U' n'`
   ([LiLiangYuZhou2024, Lemma 3.2]), each active key `u ∈ S` stores its `M`-bit word `mem` in slot
   `matching h S hm ⟨u, hu⟩ : Fin n'`.

At fixed leaf capacity `m = n'` (`FixedEncoded U' n' X`), `bitWidth_le_infoBits_add_two` proves that
the total fixed bit budget `⌈log₂(C(U', n') * K ^ n')⌉ + n' * M` exceeds the information-theoretic
benchmark `⌈log₂(C(U', n') * X ^ n')⌉` by at most `2` bits, `lookupHeader` specifies the shared
metadata-only lookup table of size `U' * C(U', n') * K ^ n' ≤ U' * C(U', n') * (2 * n') ^ n'` so
`query` inspects at most one payload slot, and `insert` / `delete` / `replace` relocate `O(T)` slots
(`O(log (max n' 2))` in expectation under uniform permutations).

## Scope note

This module supplies the pure mathematical leaf-minimap specification for the
large-parameter-regime dynamic dictionary of [LiLiangYuZhou2024, Section 5]. Word-RAM precomputed
lookup-table and bit-packed `M`-bit slot evaluation, variable-length `r > 1` outer-spillover
minimaps inside adapter trees (Section 4), strong history independence, dynamic resizing, and
super-polynomial key universes are not formalized here.

## Main definitions

* `Cslib.DataStructure.Dictionary.Minimap.headerEquiv`: computable header bijection onto
  `Fin (U'.choose m * K ^ m)` via `Cslib.BitString.subsetEquiv`.
* `Cslib.DataStructure.Dictionary.Minimap.headerUniv`, `headerBits`, `bitWidth`, `infoBits`:
  bit-budget and universe parameters.
* `Cslib.DataStructure.Dictionary.Minimap.Encoded`, `FixedEncoded`, `BoundedEncoded`: size-indexed,
  fixed-capacity leaf, and bounded-capacity (`0 ≤ m ≤ n'`) minimap states.
* `Cslib.DataStructure.Dictionary.Minimap.activeSet`, `lookupHeader`, `queryFin`, `query`, `decode`,
  `encode`, `empty`, `insertNew`, `overwrite`, `deleteMem`, `replace`, `slotDiff`: active-key set,
  metadata lookup, encoding, updates, and slot-relocation distance.

## Main results

* `bitWidth_le_infoBits_add_two`, `queryTableSize_le`: fixed leaf bit-redundancy (`≤ 2` bits) and
  shared lookup-table size bound ([LiLiangYuZhou2024, Lemma 3.7]).
* `query_encode`, `decode_encode`, `query_insertNew`, `query_overwrite`, `query_deleteMem`,
  `query_replace`, `BoundedEncoded.query_insert`, `BoundedEncoded.query_delete`,
  `BoundedEncoded.activeSet_delete`: exact lookup, active-set, and update semantics.
* `wellFormed_encode`, `wellFormed_replace`, `unusedSlotsZero_insertNew`,
  `unusedSlotsZero_overwrite`, `unusedSlotsZero_deleteMem`, `eq_of_query_eq`,
  `eq_of_query_eq_fixed`:
  invariant preservation and canonical (history-independent) uniqueness of `Encoded` /
  `FixedEncoded` from `query`.
* `slotDiff_insertNew_le`, `slotDiff_overwrite_le`, `slotDiff_deleteMem_le`, `slotDiff_replace_le`,
  `expect_slotDiff_insertNew_le`, `expect_slotDiff_insertNew_encode_le`,
  `expect_slotDiff_deleteMem_le`, `expect_slotDiff_deleteMem_encode_le`,
  `expect_slotDiff_replace_le`, `expect_slotDiff_replace_encode_le`:
  deterministic `O(T)` and expected `O(log (max n' 2))` slot-relocation bounds.

## References

* [T. Li, J. Liang, H. Yu, and R. Zhou,
  *Dynamic Dictionary with Subconstant Wasted Bits per Key*][LiLiangYuZhou2024]
* [M. Pătrașcu, *Succincter*][Patrascu2008]
-/

public section

namespace Cslib.DataStructure.Dictionary.Minimap

open Finset
open scoped BigOperators

/-! ### Header bijection, bit-budget parameters, and minimap state -/

/-- Computable bijection packing an `m`-subset `S ⊆ Fin U'` and its `m` spillover values
`Fin m → Fin K` (listed in increasing order of key in `S`) into `Fin (U'.choose m * K ^ m)`. -/
def headerEquiv (U' m K : ℕ) :
    ({ S : Finset (Fin U') // S.card = m } × (Fin m → Fin K)) ≃ Fin (U'.choose m * K ^ m) :=
  (Equiv.prodCongr (Cslib.BitString.subsetEquiv U' m) finFunctionFinEquiv).trans finProdFinEquiv

/-! ### Bit-budget parameters, minimap state, and shared lookup table -/

/-- Metadata universe size `C(U', m) * K ^ m` for `m` active keys. -/
abbrev headerUniv (U' n' X m : ℕ) : ℕ :=
  U'.choose m * (Spillover.spillUniv X n') ^ m

/-- Fixed bit width `⌈log₂(C(U', m) * K ^ m)⌉` of the metadata header. -/
@[expose]
def headerBits (U' n' X m : ℕ) : ℕ :=
  Nat.clog 2 (headerUniv U' n' X m)

/-- Total fixed bit width `⌈log₂(C(U', n') * K ^ n')⌉ + n' * M` of a full-capacity leaf minimap
(`Section 5.2`). -/
@[expose]
def bitWidth (U' n' X : ℕ) : ℕ :=
  headerBits U' n' X n' + n' * Spillover.memBits X n'

/-- Exact ceiling `⌈log₂(C(U', n') * X ^ n')⌉` of the information-theoretic leaf bit benchmark. -/
@[expose]
def infoBits (U' n' X : ℕ) : ℕ :=
  Nat.clog 2 (U'.choose n' * X ^ n')

/-- Sharp fixed-capacity leaf bit-redundancy bound (`Lemma 3.7` at `r = 1` rounded to a fixed bit
width in `Section 5.2`): `bitWidth U' n' X ≤ infoBits U' n' X + 2`. -/
theorem bitWidth_le_infoBits_add_two {U' n' X : ℕ} (hn1 : 1 ≤ n') (hnU : n' ≤ U') (hX : 1 ≤ X) :
    bitWidth U' n' X ≤ infoBits U' n' X + 2 :=
  Spillover.clog_mul_spillUniv_pow_add_le (Nat.choose_pos hnU) hX hn1

/-- Size bound on the shared metadata lookup table ([LiLiangYuZhou2024, Section 3.4, Lemma 3.7]):
`U' * headerUniv U' n' X n' ≤ U' * C(U', n') * (2 * n') ^ n'`. -/
theorem queryTableSize_le {U' n' X : ℕ} (hn1 : 1 ≤ n') :
    U' * headerUniv U' n' X n' ≤ U' * U'.choose n' * (2 * n') ^ n' := by
  dsimp only [headerUniv]
  rw [Nat.mul_assoc]
  exact Nat.mul_le_mul_left U'
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Spillover.spillUniv_le_two_mul hn1) n'))

/-- Minimap state with `m` active keys in `Fin U'`, `n'` memory slots, and payload bound `X`. -/
structure Encoded (U' n' X m : ℕ) where
  /-- Packed subset-plus-spillover metadata index. -/
  header : Fin (headerUniv U' n' X m)
  /-- Fixed array of `n'` memory-word slots of `Spillover.memBits X n'` bits each. -/
  slots : Fin n' → Fin (2 ^ Spillover.memBits X n')
  deriving DecidableEq

/-- Full-capacity leaf minimap (`m = n'`, `Section 5.2` of Li–Liang–Yu–Zhou 2024). -/
abbrev FixedEncoded (U' n' X : ℕ) := Encoded U' n' X n'

/-- Bounded-capacity minimap (`0 ≤ m ≤ n'` active keys in `n'` slots). -/
structure BoundedEncoded (U' n' X : ℕ) where
  /-- Current active key count `m ≤ n'`. -/
  size : Fin (n' + 1)
  /-- Underlying size-indexed minimap state. -/
  encoded : Encoded U' n' X size.val
  deriving DecidableEq

/-- Decoded `m`-subset subtype of active keys stored in `e.header`. -/
private def activeSub {U' n' X m : ℕ} (e : Encoded U' n' X m) :
    { S : Finset (Fin U') // S.card = m } :=
  ((headerEquiv U' m (Spillover.spillUniv X n')).symm e.header).1

/-- Active key set `S ⊆ Fin U'` stored in `e.header`. -/
def activeSet {U' n' X m : ℕ} (e : Encoded U' n' X m) : Finset (Fin U') :=
  (activeSub e).1

@[simp]
theorem card_activeSet {U' n' X m : ℕ} (e : Encoded U' n' X m) : (activeSet e).card = m := by
  exact (activeSub e).2

/-- Spillover tuple `Fin m → Fin K` (in increasing order of key in `activeSet e`) in `e.header`. -/
private def spillVec {U' n' X m : ℕ} (e : Encoded U' n' X m) :
    Fin m → Fin (Spillover.spillUniv X n') :=
  ((headerEquiv U' m (Spillover.spillUniv X n')).symm e.header).2

/-- Spillover value `k_u : Fin K` of an active key `u ∈ activeSet e`. -/
private def spillOfMem {U' n' X m : ℕ} (e : Encoded U' n' X m) {u : Fin U'} (hu : u ∈ activeSet e) :
    Fin (Spillover.spillUniv X n') :=
  spillVec e (((activeSet e).orderIsoOfFin (card_activeSet e)).symm ⟨u, hu⟩)

/-- Lookup helper operating on a decoded `(subset, spillVec)` header pair. -/
private def lookupDecoded {U' n' X m : ℕ} (h : DynamicMatching.Scheme U' n') :
    { S : Finset (Fin U') // S.card = m } × (Fin m → Fin (Spillover.spillUniv X n')) →
      Fin U' → Option (Fin (Spillover.spillUniv X n') × Fin n')
  | (⟨S, hS⟩, sv), u =>
    if hu : u ∈ S then
      (DynamicMatching.matchOpt h S u).map fun b =>
        (sv ((S.orderIsoOfFin hS).symm ⟨u, hu⟩), b)
    else
      none

/-- Shared metadata-only lookup function (`Lemma 3.7` first lookup table, `Section 5.6` metadata
probe): given scheme `h`, header `hdr`, and queried key `u`, returns `some (k_u, slotIdx)` if `u`
is active and matched, or `none` otherwise, without inspecting any payload slots. -/
def lookupHeader {U' n' X m : ℕ} (h : DynamicMatching.Scheme U' n')
    (hdr : Fin (headerUniv U' n' X m)) (u : Fin U') :
    Option (Fin (Spillover.spillUniv X n') × Fin n') :=
  lookupDecoded h ((headerEquiv U' m (Spillover.spillUniv X n')).symm hdr) u

/-- Look up `u : Fin U'` in `e` as an `Option (Fin X)`, reading `e.header` via `lookupHeader` and
at most one slot `e.slots b`. -/
@[expose]
def queryFin {U' n' X m : ℕ} (h : DynamicMatching.Scheme U' n') (e : Encoded U' n' X m)
    (u : Fin U') : Option (Fin X) :=
  match lookupHeader h e.header u with
  | none => none
  | some (k, b) => Spillover.decode? n' (k, e.slots b)

/-- Look up `u : Fin U'` in `e` as an `Option ℕ` (`Dictionary.State U'` convention). -/
@[expose]
def query {U' n' X m : ℕ} (h : DynamicMatching.Scheme U' n') (e : Encoded U' n' X m)
    (u : Fin U') : Option ℕ :=
  (queryFin h e u).map Fin.val

/-- Decode `e` to an abstract `Dictionary.State U'`. -/
@[expose]
def decode {U' n' X m : ℕ} (h : DynamicMatching.Scheme U' n') (e : Encoded U' n' X m) :
    Dictionary.State U' :=
  query h e

/-- Number of payload slots in `Fin n'` whose stored `M`-bit words differ between `e₁` and `e₂`. -/
@[expose]
def slotDiff {U' n' X m₁ m₂ : ℕ} (e₁ : Encoded U' n' X m₁) (e₂ : Encoded U' n' X m₂) : ℕ :=
  (Finset.univ.filter fun b : Fin n' => e₁.slots b ≠ e₂.slots b).card

/-- Well-formedness of an encoded minimap state: every active key's `(spillover, slot)` pair lies in
the valid range `< X` of `Spillover.decodeVal`. -/
def WellFormed {U' n' X m : ℕ} (hm : m ≤ n') (h : DynamicMatching.Scheme U' n')
    (e : Encoded U' n' X m) : Prop :=
  ∀ u (hu : u ∈ activeSet e),
    Spillover.decodeVal (spillOfMem e hu,
      e.slots (DynamicMatching.matching h (activeSet e)
        ((card_activeSet e).le.trans hm) ⟨u, hu⟩)) < X

private def lookupByInj {m n' : ℕ} {α : Type*} (f : Fin m → Fin n') (vals : Fin m → α)
    (defaultVal : α) (b : Fin n') : α :=
  match Fin.find? (fun i => f i == b) with
  | some i => vals i
  | none => defaultVal

private theorem lookupByInj_apply {m n' : ℕ} {α : Type*} {f : Fin m → Fin n'}
    (hf : Function.Injective f) (vals : Fin m → α) (defaultVal : α) (i₀ : Fin m) :
    lookupByInj f vals defaultVal (f i₀) = vals i₀ := by
  dsimp only [lookupByInj]
  cases hfind : Fin.find? (fun j => f j == f i₀) with
  | some i =>
    have htrue := Fin.eq_true_of_find?_eq_some (p := fun j => f j == f i₀) hfind
    rw [hf (eq_of_beq htrue)]
  | none =>
    have hfalse := Fin.find?_eq_none_iff.mp hfind i₀
    simp at hfalse

private theorem lookupByInj_of_forall_ne {m n' : ℕ} {α : Type*} (f : Fin m → Fin n')
    (vals : Fin m → α) (defaultVal : α) {b : Fin n'} (hne : ∀ i, f i ≠ b) :
    lookupByInj f vals defaultVal b = defaultVal := by
  dsimp only [lookupByInj]
  cases hfind : Fin.find? (fun j => f j == b) with
  | some i =>
    have htrue := Fin.eq_true_of_find?_eq_some (p := fun j => f j == b) hfind
    exact absurd (eq_of_beq htrue) (hne i)
  | none => rfl

/-! ### Canonical packing, encoding, and dynamic update operations -/

/-- Pack an `m`-subset `S ⊆ Fin U'` and per-key `(spillover, slotWord)` pairs into `Encoded`,
placing each active key's slot word at its `DynamicMatching.matching` slot and `0` in unused
slots. -/
private def packPairs {U' n' X m : ℕ} (hm : m ≤ n')
    (h : DynamicMatching.Scheme U' n') (S : Finset (Fin U')) (hS : S.card = m)
    (pairs : (a : Fin U') → a ∈ S →
      Fin (Spillover.spillUniv X n') × Fin (2 ^ Spillover.memBits X n')) :
    Encoded U' n' X m where
  header := headerEquiv U' m (Spillover.spillUniv X n')
    (⟨S, hS⟩, fun i => (pairs (S.orderEmbOfFin hS i) (S.orderEmbOfFin_mem hS i)).1)
  slots := lookupByInj
    (fun i => DynamicMatching.matching h S (hS.le.trans hm)
      ⟨S.orderEmbOfFin hS i, S.orderEmbOfFin_mem hS i⟩)
    (fun i => (pairs (S.orderEmbOfFin hS i) (S.orderEmbOfFin_mem hS i)).2)
    ⟨0, Nat.two_pow_pos _⟩

@[simp]
private theorem activeSet_packPairs {U' n' X m : ℕ} (hm : m ≤ n')
    (h : DynamicMatching.Scheme U' n') (S : Finset (Fin U')) (hS : S.card = m)
    (pairs : (a : Fin U') → a ∈ S →
      Fin (Spillover.spillUniv X n') × Fin (2 ^ Spillover.memBits X n')) :
    activeSet (packPairs hm h S hS pairs) = S := by
  simp [activeSet, activeSub, packPairs]


/-- Read `(spillover, slotWord)` of key `u` from `e` via `lookupHeader` and one slot access. -/
private def unpackPair? {U' n' X m : ℕ} (h : DynamicMatching.Scheme U' n') (e : Encoded U' n' X m)
    (u : Fin U') : Option (Fin (Spillover.spillUniv X n') × Fin (2 ^ Spillover.memBits X n')) :=
  (lookupHeader h e.header u).map fun kb => (kb.1, e.slots kb.2)

private theorem queryFin_eq_unpackPair?_bind {U' n' X m : ℕ} (h : DynamicMatching.Scheme U' n')
    (e : Encoded U' n' X m) (u : Fin U') :
    queryFin h e u = (unpackPair? h e u).bind (Spillover.decode? n') := by
  dsimp only [queryFin, unpackPair?]
  cases lookupHeader h e.header u <;> rfl

private theorem unpackPair?_of_notMem {U' n' X m : ℕ} (h : DynamicMatching.Scheme U' n')
    (e : Encoded U' n' X m) {u : Fin U'} (hu : u ∉ activeSet e) :
    unpackPair? h e u = none := by
  dsimp only [unpackPair?, lookupHeader]
  dsimp only [activeSet, activeSub] at hu
  revert hu
  rcases (headerEquiv U' m (Spillover.spillUniv X n')).symm e.header with ⟨⟨S, hS⟩, sv⟩
  intro hu
  simp [lookupDecoded, hu]

theorem queryFin_of_notMem {U' n' X m : ℕ} (h : DynamicMatching.Scheme U' n')
    (e : Encoded U' n' X m) {u : Fin U'} (hu : u ∉ activeSet e) :
    queryFin h e u = none := by
  rw [queryFin_eq_unpackPair?_bind, unpackPair?_of_notMem h e hu]; rfl

private theorem unpackPair?_isSome {U' n' X m : ℕ} (hm : m ≤ n')
    (h : DynamicMatching.Scheme U' n') (e : Encoded U' n' X m) {u : Fin U'}
    (hu : u ∈ activeSet e) : (unpackPair? h e u).isSome = true := by
  dsimp only [unpackPair?, lookupHeader]
  dsimp only [activeSet, activeSub] at hu
  revert hu
  rcases (headerEquiv U' m (Spillover.spillUniv X n')).symm e.header with ⟨⟨S, hS⟩, sv⟩
  intro hu
  dsimp only [lookupDecoded]
  simp only [hu, ↓reduceDIte, Option.isSome_map]
  have hcard : S.card ≤ n' := hS.le.trans hm
  exact (DynamicMatching.matchOpt_isSome_iff h hcard u).mpr hu

/-- Total extraction of `(spillover, slotWord)` for an active key `a ∈ activeSet e`. -/
private def unpackPair {U' n' X m : ℕ} (hm : m ≤ n')
    (h : DynamicMatching.Scheme U' n') (e : Encoded U' n' X m) {a : Fin U'}
    (ha : a ∈ activeSet e) : Fin (Spillover.spillUniv X n') × Fin (2 ^ Spillover.memBits X n') :=
  (unpackPair? h e a).get (unpackPair?_isSome hm h e ha)

private theorem unpackPair_eq {U' n' X m : ℕ} (hm : m ≤ n')
    (h : DynamicMatching.Scheme U' n') (e : Encoded U' n' X m) {a : Fin U'}
    (ha : a ∈ activeSet e) :
    unpackPair hm h e ha =
      (spillOfMem e ha,
        e.slots (DynamicMatching.matching h (activeSet e)
          ((card_activeSet e).le.trans hm) ⟨a, ha⟩)) := by
  apply Option.some.inj
  have hget : some (unpackPair hm h e ha) = unpackPair? h e a := Option.some_get _
  rw [hget]
  have hgen : ∀ (dec : { S : Finset (Fin U') // S.card = m } ×
        (Fin m → Fin (Spillover.spillUniv X n')))
      (ha' : a ∈ dec.1.1),
      (lookupDecoded h dec a).map (fun kb => (kb.1, e.slots kb.2)) =
        some (dec.2 ((dec.1.1.orderIsoOfFin dec.1.2).symm ⟨a, ha'⟩),
          e.slots (DynamicMatching.matching h dec.1.1 (dec.1.2.le.trans hm) ⟨a, ha'⟩)) := by
    rintro ⟨⟨S, hS⟩, sv⟩ ha'
    have hmatch := DynamicMatching.matching_apply h S (hS.le.trans hm) ⟨a, ha'⟩
    simp [lookupDecoded, ha', hmatch]
  exact hgen ((headerEquiv U' m (Spillover.spillUniv X n')).symm e.header) ha

@[simp]
private theorem decode?_unpackPair {U' n' X m : ℕ} (hm : m ≤ n')
    (h : DynamicMatching.Scheme U' n') (e : Encoded U' n' X m) {a : Fin U'}
    (ha : a ∈ activeSet e) :
    Spillover.decode? n' (unpackPair hm h e ha) = queryFin h e a := by
  have hget : some (unpackPair hm h e ha) = unpackPair? h e a := Option.some_get _
  rw [queryFin_eq_unpackPair?_bind, ← hget]
  rfl

private theorem unpackPair?_packPairs {U' n' X m : ℕ} (hm : m ≤ n')
    (h : DynamicMatching.Scheme U' n') (S : Finset (Fin U')) (hS : S.card = m)
    (pairs : (a : Fin U') → a ∈ S →
      Fin (Spillover.spillUniv X n') × Fin (2 ^ Spillover.memBits X n'))
    (u : Fin U') :
    unpackPair? h (packPairs hm h S hS pairs) u =
      if hu : u ∈ S then some (pairs u hu) else none := by
  have hSle : S.card ≤ n' := hS.le.trans hm
  let idxMap : Fin m → Fin n' := fun i =>
    DynamicMatching.matching h S hSle ⟨S.orderEmbOfFin hS i, S.orderEmbOfFin_mem hS i⟩
  have hinj : Function.Injective idxMap := fun i₁ i₂ heq => by
    have hsub := (DynamicMatching.matching h S hSle).injective heq
    exact (S.orderEmbOfFin hS).injective (congrArg Subtype.val hsub)
  dsimp only [unpackPair?, lookupHeader, packPairs]
  rw [Equiv.symm_apply_apply]
  dsimp only [lookupDecoded]
  by_cases hu : u ∈ S
  · simp only [hu, ↓reduceDIte]
    set i₀ : Fin m := (S.orderIsoOfFin hS).symm ⟨u, hu⟩
    have hi₀_val : S.orderEmbOfFin hS i₀ = u := by
      change ↑(S.orderIsoOfFin hS ((S.orderIsoOfFin hS).symm ⟨u, hu⟩)) = u
      simp
    have hmatch : DynamicMatching.matchOpt h S u = some (idxMap i₀) := by
      have hsub : (⟨S.orderEmbOfFin hS i₀, S.orderEmbOfFin_mem hS i₀⟩ : S) = ⟨u, hu⟩ :=
        Subtype.ext hi₀_val
      dsimp only [idxMap]
      rw [hsub]
      exact DynamicMatching.matching_apply h S hSle ⟨u, hu⟩
    rw [hmatch]
    dsimp only [Option.map]
    have hslot := lookupByInj_apply hinj
      (fun i => (pairs (S.orderEmbOfFin hS i) (S.orderEmbOfFin_mem hS i)).2)
      ⟨0, Nat.two_pow_pos _⟩ i₀
    dsimp only [idxMap] at hslot
    rw [hslot]
    congr 1
    have hpair : ∀ (a : Fin U') (ha : a ∈ S), a = u → pairs a ha = pairs u hu := by
      rintro a ha rfl; rfl
    have heq := hpair (S.orderEmbOfFin hS i₀) (S.orderEmbOfFin_mem hS i₀) hi₀_val
    exact Prod.ext (congrArg Prod.fst heq) (congrArg Prod.snd heq)
  · simp [hu]

@[simp]
private theorem unpackPair_packPairs {U' n' X m : ℕ} (hm : m ≤ n')
    (h : DynamicMatching.Scheme U' n') (S : Finset (Fin U')) (hS : S.card = m)
    (pairs : (a : Fin U') → a ∈ S →
      Fin (Spillover.spillUniv X n') × Fin (2 ^ Spillover.memBits X n'))
    {a : Fin U'} (ha' : a ∈ activeSet (packPairs hm h S hS pairs)) (ha : a ∈ S) :
    unpackPair hm h (packPairs hm h S hS pairs) ha' = pairs a ha := by
  apply Option.some.inj
  have hget : some (unpackPair hm h (packPairs hm h S hS pairs) ha') =
      unpackPair? h (packPairs hm h S hS pairs) a := Option.some_get _
  rw [hget, unpackPair?_packPairs]
  simp [ha]

private theorem queryFin_packPairs {U' n' X m : ℕ} (hm : m ≤ n')
    (h : DynamicMatching.Scheme U' n') (S : Finset (Fin U')) (hS : S.card = m)
    (pairs : (a : Fin U') → a ∈ S →
      Fin (Spillover.spillUniv X n') × Fin (2 ^ Spillover.memBits X n'))
    (u : Fin U') :
    queryFin h (packPairs hm h S hS pairs) u =
      if hu : u ∈ S then Spillover.decode? n' (pairs u hu) else none := by
  rw [queryFin_eq_unpackPair?_bind, unpackPair?_packPairs]
  by_cases hu : u ∈ S
  · simp only [hu, ↓reduceDIte]; rfl
  · simp only [hu, ↓reduceDIte]; rfl

private def valFin {U' X : ℕ} (s : Dictionary.State U') (hb : Dictionary.ValuesBounded X s)
    {u : Fin U'} (hu : u ∈ Dictionary.dom s) : Fin X :=
  match hs : s u with
  | some v => ⟨v, hb u v hs⟩
  | none => False.elim (by simp [hs] at hu)

private theorem some_valFin {U' X : ℕ} (s : Dictionary.State U')
    (hb : Dictionary.ValuesBounded X s) {u : Fin U'} (hu : u ∈ Dictionary.dom s) :
    some (valFin s hb hu).val = s u := by
  dsimp only [valFin]
  split
  · rename_i v hs; exact hs.symm
  · rename_i hs; simp [hs] at hu

/-- Encode an abstract `Dictionary.State U'` of cardinality `m ≤ n'` with values `< X`. -/
def encode {U' n' X m : ℕ} (hm : m ≤ n') (h : DynamicMatching.Scheme U' n')
    (s : Dictionary.State U') (hb : Dictionary.ValuesBounded X s)
    (hs : (Dictionary.dom s).card = m) : Encoded U' n' X m :=
  packPairs hm h (Dictionary.dom s) hs fun _ ha => Spillover.encode n' (valFin s hb ha)

/-- Empty `0`-key minimap on `n'` slots. -/
def empty (U' n' X : ℕ) : Encoded U' n' X 0 where
  header := ⟨0, by simp [headerUniv]⟩
  slots := fun _ => ⟨0, Nat.two_pow_pos _⟩

@[simp]
theorem activeSet_empty (U' n' X : ℕ) : activeSet (empty U' n' X) = ∅ :=
  card_eq_zero.mp (card_activeSet (empty U' n' X))

@[simp]
theorem activeSet_encode {U' n' X m : ℕ} (hm : m ≤ n')
    (h : DynamicMatching.Scheme U' n') (s : Dictionary.State U')
    (hb : Dictionary.ValuesBounded X s) (hs : (Dictionary.dom s).card = m) :
    activeSet (encode hm h s hb hs) = Dictionary.dom s :=
  activeSet_packPairs _ _ _ _ _

@[simp]
theorem query_encode {U' n' X m : ℕ} (hm : m ≤ n')
    (h : DynamicMatching.Scheme U' n') (s : Dictionary.State U')
    (hb : Dictionary.ValuesBounded X s) (hs : (Dictionary.dom s).card = m) (u : Fin U') :
    query h (encode hm h s hb hs) u = s u := by
  dsimp only [query, encode]
  rw [queryFin_packPairs]
  by_cases hu : u ∈ Dictionary.dom s
  · simp [hu, some_valFin s hb hu]
  · have hnone : s u = none := Option.not_isSome_iff_eq_none.mp (by simpa using hu)
    simp [hu, hnone]

@[simp]
theorem decode_encode {U' n' X m : ℕ} (hm : m ≤ n')
    (h : DynamicMatching.Scheme U' n') (s : Dictionary.State U')
    (hb : Dictionary.ValuesBounded X s) (hs : (Dictionary.dom s).card = m) :
    decode h (encode hm h s hb hs) = s :=
  funext (query_encode hm h s hb hs)

/-! ### Direct encoded-space updates (`insert`, `delete`, `replace`) -/

/-- Insert a fresh key `u ∉ activeSet e` with value `v < X`, advancing active size `m` to
`m + 1 ≤ n'`. -/
def insertNew {U' n' X m : ℕ} (hm' : m + 1 ≤ n')
    (h : DynamicMatching.Scheme U' n') (e : Encoded U' n' X m) (u : Fin U') (v : ℕ)
    (hv : v < X) (hu : u ∉ activeSet e) : Encoded U' n' X (m + 1) :=
  packPairs hm' h (insert u (activeSet e))
    (by rw [card_insert_of_notMem hu, card_activeSet])
    fun a ha =>
      if hau : a = u then
        Spillover.encode n' ⟨v, hv⟩
      else
        unpackPair (Nat.le_of_succ_le hm') h e (a := a) <| by
          rcases mem_insert.mp ha with rfl | hmem
          · exact absurd rfl hau
          · exact hmem

/-- Overwrite the value of an existing key `u ∈ activeSet e` with `v < X` in place. -/
def overwrite {U' n' X m : ℕ} (hm : m ≤ n')
    (h : DynamicMatching.Scheme U' n') (e : Encoded U' n' X m) (u : Fin U') (v : ℕ)
    (hv : v < X) (_hu : u ∈ activeSet e) : Encoded U' n' X m :=
  packPairs hm h (activeSet e) (card_activeSet e) fun a ha =>
    if a = u then Spillover.encode n' ⟨v, hv⟩ else unpackPair hm h e ha

/-- Delete an active key `u ∈ activeSet e`, reducing active size `m + 1` to `m`. -/
def deleteMem {U' n' X m : ℕ} (hm' : m + 1 ≤ n')
    (h : DynamicMatching.Scheme U' n') (e : Encoded U' n' X (m + 1)) (u : Fin U')
    (hu : u ∈ activeSet e) : Encoded U' n' X m :=
  packPairs (Nat.le_of_succ_le hm') h ((activeSet e).erase u)
    (by have hc := card_erase_of_mem hu; rw [card_activeSet] at hc; exact hc)
    fun a ha => unpackPair hm' h e (mem_of_mem_erase ha)

/-- Atomic fixed-capacity leaf key replacement (`Section 5.2` leaf minimap update): removes
`x_old ∈ activeSet e` and inserts `(x_new, v_new)` (`x_new ∉ (activeSet e).erase x_old`, covering
both fresh `x_new ∉ activeSet e` and in-place `x_new = x_old`) at fixed capacity `n'`. -/
def replace {U' n' X : ℕ} (h : DynamicMatching.Scheme U' n')
    (e : FixedEncoded U' n' X) (x_old x_new : Fin U') (v_new : ℕ) (hv : v_new < X)
    (hx_old : x_old ∈ activeSet e) (hx_new : x_new ∉ (activeSet e).erase x_old) :
    FixedEncoded U' n' X :=
  have hcard : (insert x_new ((activeSet e).erase x_old)).card = n' := by
    have hpos : 1 ≤ n' := by
      have hc : 0 < (activeSet e).card := card_pos.mpr ⟨x_old, hx_old⟩
      rw [card_activeSet] at hc; exact hc
    rw [card_insert_of_notMem hx_new, card_erase_of_mem hx_old, card_activeSet]
    omega
  packPairs le_rfl h (insert x_new ((activeSet e).erase x_old)) hcard fun a ha =>
    if han : a = x_new then
      Spillover.encode n' ⟨v_new, hv⟩
    else
      have ha_old : a ∈ activeSet e := mem_of_mem_erase ((mem_insert.mp ha).resolve_left han)
      unpackPair le_rfl h e ha_old

@[simp]
theorem activeSet_insertNew {U' n' X m : ℕ} (hm' : m + 1 ≤ n')
    (h : DynamicMatching.Scheme U' n') (e : Encoded U' n' X m) (u : Fin U') (v : ℕ)
    (hv : v < X) (hu : u ∉ activeSet e) :
    activeSet (insertNew hm' h e u v hv hu) = insert u (activeSet e) :=
  activeSet_packPairs _ _ _ _ _

@[simp]
theorem activeSet_overwrite {U' n' X m : ℕ} (hm : m ≤ n')
    (h : DynamicMatching.Scheme U' n') (e : Encoded U' n' X m) (u : Fin U') (v : ℕ)
    (hv : v < X) (hu : u ∈ activeSet e) :
    activeSet (overwrite hm h e u v hv hu) = activeSet e :=
  activeSet_packPairs _ _ _ _ _

@[simp]
theorem activeSet_deleteMem {U' n' X m : ℕ} (hm' : m + 1 ≤ n')
    (h : DynamicMatching.Scheme U' n') (e : Encoded U' n' X (m + 1)) (u : Fin U')
    (hu : u ∈ activeSet e) :
    activeSet (deleteMem hm' h e u hu) = (activeSet e).erase u :=
  activeSet_packPairs _ _ _ _ _

@[simp]
theorem activeSet_replace {U' n' X : ℕ} (h : DynamicMatching.Scheme U' n')
    (e : FixedEncoded U' n' X) (x_old x_new : Fin U') (v_new : ℕ) (hv : v_new < X)
    (hx_old : x_old ∈ activeSet e) (hx_new : x_new ∉ (activeSet e).erase x_old) :
    activeSet (replace h e x_old x_new v_new hv hx_old hx_new) =
      insert x_new ((activeSet e).erase x_old) := by
  unfold replace
  exact activeSet_packPairs _ _ _ _ _

@[simp]
theorem query_insertNew {U' n' X m : ℕ} (hm' : m + 1 ≤ n')
    (h : DynamicMatching.Scheme U' n') (e : Encoded U' n' X m) (u : Fin U') (v : ℕ)
    (hv : v < X) (hu : u ∉ activeSet e) (u' : Fin U') :
    query h (insertNew hm' h e u v hv hu) u' = Function.update (query h e) u (some v) u' := by
  by_cases heq : u' = u
  · subst heq
    dsimp only [query, insertNew]
    rw [queryFin_packPairs]
    simp
  · rw [Function.update_of_ne heq]
    dsimp only [query, insertNew]
    rw [queryFin_packPairs]
    by_cases hmem : u' ∈ activeSet e
    · simp [hmem, heq]
    · simp [hmem, heq, queryFin_of_notMem h e hmem]

@[simp]
theorem query_overwrite {U' n' X m : ℕ} (hm : m ≤ n')
    (h : DynamicMatching.Scheme U' n') (e : Encoded U' n' X m) (u : Fin U') (v : ℕ)
    (hv : v < X) (hu : u ∈ activeSet e) (u' : Fin U') :
    query h (overwrite hm h e u v hv hu) u' = Function.update (query h e) u (some v) u' := by
  by_cases heq : u' = u
  · subst heq
    dsimp only [query, overwrite]
    rw [queryFin_packPairs]
    simp [hu]
  · rw [Function.update_of_ne heq]
    dsimp only [query, overwrite]
    rw [queryFin_packPairs]
    by_cases hmem : u' ∈ activeSet e
    · simp [hmem, heq]
    · simp [hmem, queryFin_of_notMem h e hmem]

@[simp]
theorem query_deleteMem {U' n' X m : ℕ} (hm' : m + 1 ≤ n')
    (h : DynamicMatching.Scheme U' n') (e : Encoded U' n' X (m + 1)) (u : Fin U')
    (hu : u ∈ activeSet e) (u' : Fin U') :
    query h (deleteMem hm' h e u hu) u' = Function.update (query h e) u none u' := by
  by_cases heq : u' = u
  · subst heq
    dsimp only [query, deleteMem]
    rw [queryFin_packPairs]
    simp
  · rw [Function.update_of_ne heq]
    dsimp only [query, deleteMem]
    rw [queryFin_packPairs]
    by_cases hmem : u' ∈ activeSet e
    · simp [hmem, heq]
    · simp [hmem, heq, queryFin_of_notMem h e hmem]

@[simp]
theorem query_replace {U' n' X : ℕ} (h : DynamicMatching.Scheme U' n')
    (e : FixedEncoded U' n' X) (x_old x_new : Fin U') (v_new : ℕ) (hv : v_new < X)
    (hx_old : x_old ∈ activeSet e) (hx_new : x_new ∉ (activeSet e).erase x_old) (u' : Fin U') :
    query h (replace h e x_old x_new v_new hv hx_old hx_new) u' =
      Function.update (Function.update (query h e) x_old none) x_new (some v_new) u' := by
  by_cases hnew : u' = x_new
  · subst hnew
    dsimp only [query, replace]
    rw [queryFin_packPairs]
    simp
  · rw [Function.update_of_ne hnew]
    by_cases hold : u' = x_old
    · subst hold
      dsimp only [query, replace]
      rw [queryFin_packPairs]
      simp [hnew]
    · rw [Function.update_of_ne hold]
      dsimp only [query, replace]
      rw [queryFin_packPairs]
      by_cases hmem : u' ∈ activeSet e
      · simp [hmem, hnew, hold]
      · simp [hmem, hnew, hold, queryFin_of_notMem h e hmem]

namespace BoundedEncoded

/-- Empty bounded-capacity minimap (`0` active keys). -/
def empty (U' n' X : ℕ) : BoundedEncoded U' n' X :=
  ⟨⟨0, Nat.zero_lt_succ n'⟩, Minimap.empty U' n' X⟩

/-- Encode an abstract `Dictionary.State U'` of size `≤ n'` with values `< X`. -/
def encode {U' n' X : ℕ} (h : DynamicMatching.Scheme U' n')
    (s : Dictionary.State U') (hb : Dictionary.ValuesBounded X s)
    (hs : (Dictionary.dom s).card ≤ n') : BoundedEncoded U' n' X :=
  ⟨⟨(Dictionary.dom s).card, Nat.lt_succ_of_le hs⟩, Minimap.encode hs h s hb rfl⟩

/-- Look up `u : Fin U'` in a `BoundedEncoded` minimap. -/
@[expose]
def query {U' n' X : ℕ} (h : DynamicMatching.Scheme U' n') (b : BoundedEncoded U' n' X)
    (u : Fin U') : Option ℕ :=
  Minimap.query h b.encoded u

/-- Decode `b` to an abstract `Dictionary.State U'`. -/
@[expose]
def decode {U' n' X : ℕ} (h : DynamicMatching.Scheme U' n') (b : BoundedEncoded U' n' X) :
    Dictionary.State U' :=
  query h b

/-- Insert or overwrite `(u, v)` in `b` (`b.size.val < n' ∨ u ∈ activeSet b.encoded`, `v < X`). -/
def insert {U' n' X : ℕ} (h : DynamicMatching.Scheme U' n')
    (b : BoundedEncoded U' n' X) (u : Fin U') (v : ℕ) (hv : v < X)
    (hcap : b.size.val < n' ∨ u ∈ activeSet b.encoded) : BoundedEncoded U' n' X :=
  if hu : u ∈ activeSet b.encoded then
    ⟨b.size, Minimap.overwrite (Nat.le_of_lt_succ b.size.isLt) h b.encoded u v hv hu⟩
  else
    have hlt : b.size.val < n' := hcap.resolve_right hu
    ⟨⟨b.size.val + 1, Nat.succ_lt_succ hlt⟩,
      Minimap.insertNew hlt h b.encoded u v hv hu⟩

/-- Delete `u` from `b` (no-op if `u ∉ activeSet b.encoded`). -/
def delete {U' n' X : ℕ} (h : DynamicMatching.Scheme U' n')
    (b : BoundedEncoded U' n' X) (u : Fin U') : BoundedEncoded U' n' X :=
  if hu : u ∈ activeSet b.encoded then
    match b with
    | ⟨⟨0, _⟩, e⟩ => False.elim (by
        have hc := card_activeSet e
        rw [card_eq_zero.mp hc] at hu
        exact notMem_empty u hu)
    | ⟨⟨m + 1, hm⟩, e⟩ =>
      ⟨⟨m, Nat.lt_of_succ_lt hm⟩, Minimap.deleteMem (Nat.le_of_lt_succ hm) h e u hu⟩
  else
    b

@[simp]
theorem query_encode {U' n' X : ℕ} (h : DynamicMatching.Scheme U' n')
    (s : Dictionary.State U') (hb : Dictionary.ValuesBounded X s)
    (hs : (Dictionary.dom s).card ≤ n') (u : Fin U') :
    query h (encode h s hb hs) u = s u :=
  Minimap.query_encode hs h s hb rfl u

theorem size_eq_card_activeSet {U' n' X : ℕ} (b : BoundedEncoded U' n' X) :
    b.size.val = (activeSet b.encoded).card :=
  (card_activeSet b.encoded).symm

@[simp]
theorem size_empty (U' n' X : ℕ) : (empty U' n' X).size.val = 0 := by
  simp [empty]

@[simp]
theorem activeSet_empty (U' n' X : ℕ) : activeSet (empty U' n' X).encoded = ∅ := by
  simp [empty]

@[simp]
theorem activeSet_encode {U' n' X : ℕ} (h : DynamicMatching.Scheme U' n')
    (s : Dictionary.State U') (hb : Dictionary.ValuesBounded X s)
    (hs : (Dictionary.dom s).card ≤ n') :
    activeSet (encode h s hb hs).encoded = Dictionary.dom s := by
  simp [encode]

@[simp]
theorem size_encode {U' n' X : ℕ} (h : DynamicMatching.Scheme U' n')
    (s : Dictionary.State U') (hb : Dictionary.ValuesBounded X s)
    (hs : (Dictionary.dom s).card ≤ n') :
    (encode h s hb hs).size.val = (Dictionary.dom s).card := by
  simp [encode]

@[simp]
theorem activeSet_insert {U' n' X : ℕ} (h : DynamicMatching.Scheme U' n')
    (b : BoundedEncoded U' n' X) (u : Fin U') (v : ℕ) (hv : v < X)
    (hcap : b.size.val < n' ∨ u ∈ activeSet b.encoded) :
    activeSet (insert h b u v hv hcap).encoded = Insert.insert u (activeSet b.encoded) := by
  by_cases hu : u ∈ activeSet b.encoded
  · have hins : insert h b u v hv hcap =
        ⟨b.size, Minimap.overwrite (Nat.le_of_lt_succ b.size.isLt) h b.encoded u v hv hu⟩ := by
      unfold insert; simp only [hu, ↓reduceDIte]
    rw [hins, Minimap.activeSet_overwrite, insert_eq_of_mem hu]
  · have hins : insert h b u v hv hcap =
        ⟨⟨b.size.val + 1, Nat.succ_lt_succ (hcap.resolve_right hu)⟩,
          Minimap.insertNew (hcap.resolve_right hu) h b.encoded u v hv hu⟩ := by
      unfold insert; simp only [hu, ↓reduceDIte]
    rw [hins, Minimap.activeSet_insertNew]

theorem size_insert_of_notMem {U' n' X : ℕ} (h : DynamicMatching.Scheme U' n')
    (b : BoundedEncoded U' n' X) (u : Fin U') (v : ℕ) (hv : v < X)
    (hcap : b.size.val < n' ∨ u ∈ activeSet b.encoded) (hu : u ∉ activeSet b.encoded) :
    (insert h b u v hv hcap).size.val = b.size.val + 1 := by
  have hins : insert h b u v hv hcap =
      ⟨⟨b.size.val + 1, Nat.succ_lt_succ (hcap.resolve_right hu)⟩,
        Minimap.insertNew (hcap.resolve_right hu) h b.encoded u v hv hu⟩ := by
    unfold insert; simp only [hu, ↓reduceDIte]
  rw [hins]

theorem size_insert_of_mem {U' n' X : ℕ} (h : DynamicMatching.Scheme U' n')
    (b : BoundedEncoded U' n' X) (u : Fin U') (v : ℕ) (hv : v < X)
    (hcap : b.size.val < n' ∨ u ∈ activeSet b.encoded) (hu : u ∈ activeSet b.encoded) :
    (insert h b u v hv hcap).size.val = b.size.val := by
  rw [size_eq_card_activeSet, activeSet_insert, insert_eq_of_mem hu, card_activeSet]

@[simp]
theorem activeSet_delete {U' n' X : ℕ} (h : DynamicMatching.Scheme U' n')
    (b : BoundedEncoded U' n' X) (u : Fin U') :
    activeSet (delete h b u).encoded = (activeSet b.encoded).erase u := by
  rcases b with ⟨⟨m, hm⟩, e⟩
  by_cases hu : u ∈ activeSet e
  · cases m with
    | zero =>
      have hc := card_activeSet e
      rw [card_eq_zero.mp hc] at hu
      exact False.elim (notMem_empty u hu)
    | succ m =>
      have hdel : delete h ⟨⟨m + 1, hm⟩, e⟩ u =
          ⟨⟨m, Nat.lt_of_succ_lt hm⟩,
            Minimap.deleteMem (Nat.le_of_lt_succ hm) h e u hu⟩ := by
        unfold delete; simp only [hu, ↓reduceDIte]
      rw [hdel, Minimap.activeSet_deleteMem]
  · have hdel : delete h ⟨⟨m, hm⟩, e⟩ u = ⟨⟨m, hm⟩, e⟩ := by
      unfold delete; simp only [hu, ↓reduceDIte]
    rw [hdel, erase_eq_of_notMem hu]

theorem size_delete_of_mem {U' n' X : ℕ} (h : DynamicMatching.Scheme U' n')
    (b : BoundedEncoded U' n' X) (u : Fin U') (hu : u ∈ activeSet b.encoded) :
    (delete h b u).size.val = b.size.val - 1 := by
  rw [size_eq_card_activeSet, activeSet_delete, card_erase_of_mem hu, card_activeSet]

theorem size_delete_of_notMem {U' n' X : ℕ} (h : DynamicMatching.Scheme U' n')
    (b : BoundedEncoded U' n' X) (u : Fin U') (hu : u ∉ activeSet b.encoded) :
    (delete h b u).size.val = b.size.val := by
  rw [size_eq_card_activeSet, activeSet_delete, erase_eq_of_notMem hu, card_activeSet]

@[simp]
theorem query_insert {U' n' X : ℕ} (h : DynamicMatching.Scheme U' n')
    (b : BoundedEncoded U' n' X) (u : Fin U') (v : ℕ) (hv : v < X)
    (hcap : b.size.val < n' ∨ u ∈ activeSet b.encoded) (u' : Fin U') :
    query h (insert h b u v hv hcap) u' = Function.update (query h b) u (some v) u' := by
  by_cases hu : u ∈ activeSet b.encoded
  · have hins : insert h b u v hv hcap =
        ⟨b.size, Minimap.overwrite (Nat.le_of_lt_succ b.size.isLt) h b.encoded u v hv hu⟩ := by
      unfold insert
      simp only [hu, ↓reduceDIte]
    rw [hins]
    exact Minimap.query_overwrite _ h b.encoded u v hv hu u'
  · have hins : insert h b u v hv hcap =
        ⟨⟨b.size.val + 1, Nat.succ_lt_succ (hcap.resolve_right hu)⟩,
          Minimap.insertNew (hcap.resolve_right hu) h b.encoded u v hv hu⟩ := by
      unfold insert
      simp only [hu, ↓reduceDIte]
    rw [hins]
    exact Minimap.query_insertNew (hcap.resolve_right hu) h b.encoded u v hv hu u'

@[simp]
theorem query_delete {U' n' X : ℕ} (h : DynamicMatching.Scheme U' n')
    (b : BoundedEncoded U' n' X) (u u' : Fin U') :
    query h (delete h b u) u' = Function.update (query h b) u none u' := by
  rcases b with ⟨⟨m, hm⟩, e⟩
  by_cases hu : u ∈ activeSet e
  · cases m with
    | zero =>
      have hc := card_activeSet e
      rw [card_eq_zero.mp hc] at hu
      exact False.elim (notMem_empty u hu)
    | succ m =>
      have hdel : delete h ⟨⟨m + 1, hm⟩, e⟩ u =
          ⟨⟨m, Nat.lt_of_succ_lt hm⟩,
            Minimap.deleteMem (Nat.le_of_lt_succ hm) h e u hu⟩ := by
        unfold delete
        simp only [hu, ↓reduceDIte]
      rw [hdel]
      exact Minimap.query_deleteMem (Nat.le_of_lt_succ hm) h e u hu u'
  · have hdel : delete h ⟨⟨m, hm⟩, e⟩ u = ⟨⟨m, hm⟩, e⟩ := by
      unfold delete
      simp only [hu, ↓reduceDIte]
    rw [hdel]
    by_cases heq : u' = u
    · subst heq; simp [query, Minimap.query, queryFin_of_notMem h e hu]
    · simp [Function.update_of_ne heq]

end BoundedEncoded

/-! ### Canonical slot invariant, `encode` commutativity, and slot-relocation bounds -/

/-- Invariant stating that every slot `b : Fin n'` not matched to an active key holds `0`. Holds
automatically for `empty`, `encode`, `insertNew`, `overwrite`, `deleteMem`, and `replace`, is
preserved by `BoundedEncoded.delete`, and holds unconditionally for every full-capacity leaf state
`e : FixedEncoded U' n' X` (`unusedSlotsZero_fixed`). -/
@[expose]
def UnusedSlotsZero {U' n' X m : ℕ} (h : DynamicMatching.Scheme U' n')
    (e : Encoded U' n' X m) : Prop :=
  ∀ b : Fin n', (∀ a ∈ activeSet e, DynamicMatching.matchOpt h (activeSet e) a ≠ some b) →
    e.slots b = ⟨0, Nat.two_pow_pos _⟩

private theorem slots_packPairs_of_matchOpt {U' n' X m : ℕ} (hm : m ≤ n')
    (h : DynamicMatching.Scheme U' n') (S : Finset (Fin U')) (hS : S.card = m)
    (pairs : (a : Fin U') → a ∈ S →
      Fin (Spillover.spillUniv X n') × Fin (2 ^ Spillover.memBits X n'))
    {a : Fin U'} {b : Fin n'} (hab : DynamicMatching.matchOpt h S a = some b) :
    ∃ ha : a ∈ S, (packPairs hm h S hS pairs).slots b = (pairs a ha).2 := by
  have hSle : S.card ≤ n' := hS.le.trans hm
  have ha : a ∈ S := (DynamicMatching.matchOpt_isSome_iff h hSle a).mp (by rw [hab]; rfl)
  refine ⟨ha, ?_⟩
  let idxMap : Fin m → Fin n' := fun i =>
    DynamicMatching.matching h S hSle ⟨S.orderEmbOfFin hS i, S.orderEmbOfFin_mem hS i⟩
  have hinj : Function.Injective idxMap := fun i₁ i₂ heq => by
    have hsub := (DynamicMatching.matching h S hSle).injective heq
    exact (S.orderEmbOfFin hS).injective (congrArg Subtype.val hsub)
  set i₀ : Fin m := (S.orderIsoOfFin hS).symm ⟨a, ha⟩
  have hi₀_val : S.orderEmbOfFin hS i₀ = a := by
    change ↑(S.orderIsoOfFin hS ((S.orderIsoOfFin hS).symm ⟨a, ha⟩)) = a
    simp
  have hidx_eq : idxMap i₀ = b := by
    apply Option.some.inj
    have hsub : (⟨S.orderEmbOfFin hS i₀, S.orderEmbOfFin_mem hS i₀⟩ : S) = ⟨a, ha⟩ :=
      Subtype.ext hi₀_val
    dsimp only [idxMap]
    rw [hsub, ← DynamicMatching.matching_apply h S hSle ⟨a, ha⟩, hab]
  dsimp only [packPairs]
  rw [← hidx_eq]
  have hslot := lookupByInj_apply hinj
    (fun i => (pairs (S.orderEmbOfFin hS i) (S.orderEmbOfFin_mem hS i)).2)
    ⟨0, Nat.two_pow_pos _⟩ i₀
  dsimp only [idxMap] at hslot
  rw [hslot]
  have hpair : ∀ (x : Fin U') (hx : x ∈ S), x = a → pairs x hx = pairs a ha := by
    rintro x hx rfl; rfl
  exact congrArg Prod.snd (hpair _ _ hi₀_val)

private theorem slots_packPairs_of_forall_ne {U' n' X m : ℕ} (hm : m ≤ n')
    (h : DynamicMatching.Scheme U' n') (S : Finset (Fin U')) (hS : S.card = m)
    (pairs : (a : Fin U') → a ∈ S →
      Fin (Spillover.spillUniv X n') × Fin (2 ^ Spillover.memBits X n'))
    {b : Fin n'} (hnone : ∀ a ∈ S, DynamicMatching.matchOpt h S a ≠ some b) :
    (packPairs hm h S hS pairs).slots b = ⟨0, Nat.two_pow_pos _⟩ := by
  have hSle : S.card ≤ n' := hS.le.trans hm
  dsimp only [packPairs]
  refine lookupByInj_of_forall_ne _ _ _ fun i => ?_
  intro heq
  have hmem := S.orderEmbOfFin_mem hS i
  have hm_eq := DynamicMatching.matching_apply h S hSle ⟨S.orderEmbOfFin hS i, hmem⟩
  rw [heq] at hm_eq
  exact hnone _ hmem hm_eq

private theorem unusedSlotsZero_packPairs {U' n' X m : ℕ} (hm : m ≤ n')
    (h : DynamicMatching.Scheme U' n') (S : Finset (Fin U')) (hS : S.card = m)
    (pairs : (a : Fin U') → a ∈ S →
      Fin (Spillover.spillUniv X n') × Fin (2 ^ Spillover.memBits X n')) :
    UnusedSlotsZero h (packPairs hm h S hS pairs) := by
  intro b hb
  rw [activeSet_packPairs] at hb
  exact slots_packPairs_of_forall_ne hm h S hS pairs hb

theorem unusedSlotsZero_empty {U' n' X : ℕ} (h : DynamicMatching.Scheme U' n') :
    UnusedSlotsZero h (empty U' n' X) := by
  intro _ _
  simp [empty]

theorem unusedSlotsZero_encode {U' n' X m : ℕ} (hm : m ≤ n')
    (h : DynamicMatching.Scheme U' n') (s : Dictionary.State U')
    (hb : Dictionary.ValuesBounded X s) (hs : (Dictionary.dom s).card = m) :
    UnusedSlotsZero h (encode hm h s hb hs) :=
  unusedSlotsZero_packPairs hm h _ hs _

theorem unusedSlotsZero_insertNew {U' n' X m : ℕ} (hm' : m + 1 ≤ n')
    (h : DynamicMatching.Scheme U' n') (e : Encoded U' n' X m) (u : Fin U') (v : ℕ)
    (hv : v < X) (hu : u ∉ activeSet e) :
    UnusedSlotsZero h (insertNew hm' h e u v hv hu) :=
  unusedSlotsZero_packPairs hm' h _ _ _

theorem unusedSlotsZero_overwrite {U' n' X m : ℕ} (hm : m ≤ n')
    (h : DynamicMatching.Scheme U' n') (e : Encoded U' n' X m) (u : Fin U') (v : ℕ)
    (hv : v < X) (hu : u ∈ activeSet e) :
    UnusedSlotsZero h (overwrite hm h e u v hv hu) :=
  unusedSlotsZero_packPairs hm h _ _ _

theorem unusedSlotsZero_deleteMem {U' n' X m : ℕ} (hm' : m + 1 ≤ n')
    (h : DynamicMatching.Scheme U' n') (e : Encoded U' n' X (m + 1)) (u : Fin U')
    (hu : u ∈ activeSet e) :
    UnusedSlotsZero h (deleteMem hm' h e u hu) :=
  unusedSlotsZero_packPairs (Nat.le_of_succ_le hm') h _ _ _

theorem unusedSlotsZero_replace {U' n' X : ℕ} (h : DynamicMatching.Scheme U' n')
    (e : FixedEncoded U' n' X) (x_old x_new : Fin U') (v_new : ℕ) (hv : v_new < X)
    (hx_old : x_old ∈ activeSet e) (hx_new : x_new ∉ (activeSet e).erase x_old) :
    UnusedSlotsZero h (replace h e x_old x_new v_new hv hx_old hx_new) := by
  unfold replace
  exact unusedSlotsZero_packPairs le_rfl h _ _ _

/-- Every full-capacity leaf minimap `e : FixedEncoded U' n' X` (`m = n'`) satisfies
`UnusedSlotsZero h e` unconditionally because `matching` is a bijection onto `Fin n'`. -/
theorem unusedSlotsZero_fixed {U' n' X : ℕ}
    (h : DynamicMatching.Scheme U' n') (e : FixedEncoded U' n' X) :
    UnusedSlotsZero h e := by
  intro b hb
  have hS : (activeSet e).card = n' := card_activeSet e
  let emb := DynamicMatching.matching h (activeSet e) (Nat.le_of_eq hS)
  have hbij : Function.Bijective emb :=
    (Fintype.bijective_iff_injective_and_card emb).mpr ⟨emb.injective, by simp [hS]⟩
  obtain ⟨⟨a, ha⟩, hab⟩ := hbij.2 b
  have hm_eq := DynamicMatching.matching_apply h (activeSet e) (Nat.le_of_eq hS) ⟨a, ha⟩
  rw [hab] at hm_eq
  exact False.elim (hb a ha hm_eq)

private theorem unpackPair_snd_of_matchOpt {U' n' X m : ℕ} (hm : m ≤ n')
    (h : DynamicMatching.Scheme U' n') (e : Encoded U' n' X m) {a : Fin U'}
    (ha : a ∈ activeSet e) {b : Fin n'}
    (hab : DynamicMatching.matchOpt h (activeSet e) a = some b) :
    (unpackPair hm h e ha).2 = e.slots b := by
  have hm_eq := DynamicMatching.matching_apply h (activeSet e)
    ((card_activeSet e).le.trans hm) ⟨a, ha⟩
  have hb : DynamicMatching.matching h (activeSet e)
      ((card_activeSet e).le.trans hm) ⟨a, ha⟩ = b := Option.some.inj (hm_eq.symm.trans hab)
  rw [unpackPair_eq, hb]

theorem wellFormed_iff_queryFin_isSome {U' n' X m : ℕ} (hm : m ≤ n')
    (h : DynamicMatching.Scheme U' n') (e : Encoded U' n' X m) :
    WellFormed hm h e ↔ ∀ u ∈ activeSet e, (queryFin h e u).isSome = true := by
  refine ⟨fun hwf u hu => ?_, fun hq u hu => ?_⟩
  · rw [← decode?_unpackPair hm h e hu, unpackPair_eq]
    have hlt := hwf u hu
    simp [Spillover.decode?, hlt]
  · have his := hq u hu
    rw [← decode?_unpackPair hm h e hu, unpackPair_eq] at his
    dsimp only [Spillover.decode?] at his
    split_ifs at his with hlt
    · exact hlt
    · simp at his

theorem wellFormed_iff_query_isSome {U' n' X m : ℕ} (hm : m ≤ n')
    (h : DynamicMatching.Scheme U' n') (e : Encoded U' n' X m) :
    WellFormed hm h e ↔ ∀ u ∈ activeSet e, (query h e u).isSome = true := by
  simp [wellFormed_iff_queryFin_isSome hm h e, query]

theorem wellFormed_empty {U' n' X : ℕ} (h : DynamicMatching.Scheme U' n') :
    WellFormed (Nat.zero_le n') h (empty U' n' X) := by
  rw [wellFormed_iff_query_isSome]
  intro u hu
  simp at hu

theorem wellFormed_encode {U' n' X m : ℕ} (hm : m ≤ n')
    (h : DynamicMatching.Scheme U' n') (s : Dictionary.State U')
    (hb : Dictionary.ValuesBounded X s) (hs : (Dictionary.dom s).card = m) :
    WellFormed hm h (encode hm h s hb hs) := by
  rw [wellFormed_iff_query_isSome]
  intro u hu
  rw [activeSet_encode] at hu
  simpa using hu

theorem wellFormed_insertNew {U' n' X m : ℕ} (hm' : m + 1 ≤ n')
    (h : DynamicMatching.Scheme U' n') {e : Encoded U' n' X m}
    (hwf : WellFormed (Nat.le_of_succ_le hm') h e) (u : Fin U') (v : ℕ)
    (hv : v < X) (hu : u ∉ activeSet e) :
    WellFormed hm' h (insertNew hm' h e u v hv hu) := by
  rw [wellFormed_iff_query_isSome]
  intro u' hu'
  rw [query_insertNew]
  by_cases heq : u' = u
  · subst heq; simp
  · rw [Function.update_of_ne heq]
    have hmem : u' ∈ activeSet e := (mem_insert.mp (by simpa using hu')).resolve_left heq
    exact (wellFormed_iff_query_isSome (Nat.le_of_succ_le hm') h e).mp hwf u' hmem

theorem wellFormed_overwrite {U' n' X m : ℕ} (hm : m ≤ n')
    (h : DynamicMatching.Scheme U' n') {e : Encoded U' n' X m}
    (hwf : WellFormed hm h e) (u : Fin U') (v : ℕ)
    (hv : v < X) (hu : u ∈ activeSet e) :
    WellFormed hm h (overwrite hm h e u v hv hu) := by
  rw [wellFormed_iff_query_isSome]
  intro u' hu'
  rw [query_overwrite]
  by_cases heq : u' = u
  · subst heq; simp
  · rw [Function.update_of_ne heq]
    exact (wellFormed_iff_query_isSome hm h e).mp hwf u' (by simpa using hu')

theorem wellFormed_deleteMem {U' n' X m : ℕ} (hm' : m + 1 ≤ n')
    (h : DynamicMatching.Scheme U' n') {e : Encoded U' n' X (m + 1)}
    (hwf : WellFormed hm' h e) (u : Fin U') (hu : u ∈ activeSet e) :
    WellFormed (Nat.le_of_succ_le hm') h (deleteMem hm' h e u hu) := by
  rw [wellFormed_iff_query_isSome]
  intro u' hu'
  rw [activeSet_deleteMem] at hu'
  rw [query_deleteMem, Function.update_of_ne (ne_of_mem_erase hu')]
  exact (wellFormed_iff_query_isSome hm' h e).mp hwf u' (mem_of_mem_erase hu')

theorem wellFormed_replace {U' n' X : ℕ} (h : DynamicMatching.Scheme U' n')
    {e : FixedEncoded U' n' X} (hwf : WellFormed le_rfl h e)
    (x_old x_new : Fin U') (v_new : ℕ) (hv : v_new < X)
    (hx_old : x_old ∈ activeSet e) (hx_new : x_new ∉ (activeSet e).erase x_old) :
    WellFormed le_rfl h (replace h e x_old x_new v_new hv hx_old hx_new) := by
  rw [wellFormed_iff_query_isSome]
  intro u' hu'
  rw [activeSet_replace] at hu'
  rw [query_replace]
  by_cases hnew : u' = x_new
  · subst hnew; simp
  · have herase : u' ∈ (activeSet e).erase x_old := (mem_insert.mp hu').resolve_left hnew
    rw [Function.update_of_ne hnew, Function.update_of_ne (ne_of_mem_erase herase)]
    exact (wellFormed_iff_query_isSome le_rfl h e).mp hwf u' (mem_of_mem_erase herase)

namespace BoundedEncoded

/-- Well-formedness of a bounded-capacity minimap state. -/
abbrev WellFormed {U' n' X : ℕ} (h : DynamicMatching.Scheme U' n')
    (b : BoundedEncoded U' n' X) : Prop :=
  Minimap.WellFormed (Nat.le_of_lt_succ b.size.isLt) h b.encoded

theorem wellFormed_empty {U' n' X : ℕ} (h : DynamicMatching.Scheme U' n') :
    WellFormed h (empty U' n' X) :=
  Minimap.wellFormed_empty h

theorem wellFormed_encode {U' n' X : ℕ} (h : DynamicMatching.Scheme U' n')
    (s : Dictionary.State U') (hb : Dictionary.ValuesBounded X s)
    (hs : (Dictionary.dom s).card ≤ n') :
    WellFormed h (encode h s hb hs) :=
  Minimap.wellFormed_encode hs h s hb rfl

theorem wellFormed_insert {U' n' X : ℕ} (h : DynamicMatching.Scheme U' n')
    {b : BoundedEncoded U' n' X} (hwf : WellFormed h b)
    (u : Fin U') (v : ℕ) (hv : v < X)
    (hcap : b.size.val < n' ∨ u ∈ activeSet b.encoded) :
    WellFormed h (insert h b u v hv hcap) := by
  by_cases hu : u ∈ activeSet b.encoded
  · have hins : insert h b u v hv hcap =
        ⟨b.size, Minimap.overwrite (Nat.le_of_lt_succ b.size.isLt) h b.encoded u v hv hu⟩ := by
      unfold insert; simp only [hu, ↓reduceDIte]
    rw [hins]
    exact Minimap.wellFormed_overwrite _ h hwf u v hv hu
  · have hins : insert h b u v hv hcap =
        ⟨⟨b.size.val + 1, Nat.succ_lt_succ (hcap.resolve_right hu)⟩,
          Minimap.insertNew (hcap.resolve_right hu) h b.encoded u v hv hu⟩ := by
      unfold insert; simp only [hu, ↓reduceDIte]
    rw [hins]
    exact Minimap.wellFormed_insertNew (hcap.resolve_right hu) h hwf u v hv hu

theorem wellFormed_delete {U' n' X : ℕ} (h : DynamicMatching.Scheme U' n')
    {b : BoundedEncoded U' n' X} (hwf : WellFormed h b) (u : Fin U') :
    WellFormed h (delete h b u) := by
  rcases b with ⟨⟨m, hm⟩, e⟩
  by_cases hu : u ∈ activeSet e
  · cases m with
    | zero =>
      have hc := card_activeSet e
      rw [card_eq_zero.mp hc] at hu
      exact False.elim (notMem_empty u hu)
    | succ m =>
      have hdel : delete h ⟨⟨m + 1, hm⟩, e⟩ u =
          ⟨⟨m, Nat.lt_of_succ_lt hm⟩,
            Minimap.deleteMem (Nat.le_of_lt_succ hm) h e u hu⟩ := by
        unfold delete; simp only [hu, ↓reduceDIte]
      rw [hdel]
      exact Minimap.wellFormed_deleteMem (Nat.le_of_lt_succ hm) h hwf u hu
  · have hdel : delete h ⟨⟨m, hm⟩, e⟩ u = ⟨⟨m, hm⟩, e⟩ := by
      unfold delete; simp only [hu, ↓reduceDIte]
    rw [hdel]
    exact hwf

theorem unusedSlotsZero_empty {U' n' X : ℕ} (h : DynamicMatching.Scheme U' n') :
    UnusedSlotsZero h (empty U' n' X).encoded :=
  Minimap.unusedSlotsZero_empty h

theorem unusedSlotsZero_encode {U' n' X : ℕ} (h : DynamicMatching.Scheme U' n')
    (s : Dictionary.State U') (hb : Dictionary.ValuesBounded X s)
    (hs : (Dictionary.dom s).card ≤ n') :
    UnusedSlotsZero h (encode h s hb hs).encoded :=
  Minimap.unusedSlotsZero_encode hs h s hb rfl

theorem unusedSlotsZero_insert {U' n' X : ℕ} (h : DynamicMatching.Scheme U' n')
    (b : BoundedEncoded U' n' X) (u : Fin U') (v : ℕ) (hv : v < X)
    (hcap : b.size.val < n' ∨ u ∈ activeSet b.encoded) :
    UnusedSlotsZero h (insert h b u v hv hcap).encoded := by
  by_cases hu : u ∈ activeSet b.encoded
  · have hins : insert h b u v hv hcap =
        ⟨b.size, Minimap.overwrite (Nat.le_of_lt_succ b.size.isLt) h b.encoded u v hv hu⟩ := by
      unfold insert; simp only [hu, ↓reduceDIte]
    rw [hins]
    exact Minimap.unusedSlotsZero_overwrite _ h b.encoded u v hv hu
  · have hins : insert h b u v hv hcap =
        ⟨⟨b.size.val + 1, Nat.succ_lt_succ (hcap.resolve_right hu)⟩,
          Minimap.insertNew (hcap.resolve_right hu) h b.encoded u v hv hu⟩ := by
      unfold insert; simp only [hu, ↓reduceDIte]
    rw [hins]
    exact Minimap.unusedSlotsZero_insertNew (hcap.resolve_right hu) h b.encoded u v hv hu

theorem unusedSlotsZero_delete {U' n' X : ℕ} (h : DynamicMatching.Scheme U' n')
    {b : BoundedEncoded U' n' X} (hz : UnusedSlotsZero h b.encoded) (u : Fin U') :
    UnusedSlotsZero h (delete h b u).encoded := by
  rcases b with ⟨⟨m, hm⟩, e⟩
  by_cases hu : u ∈ activeSet e
  · cases m with
    | zero =>
      have hc := card_activeSet e
      rw [card_eq_zero.mp hc] at hu
      exact False.elim (notMem_empty u hu)
    | succ m =>
      have hdel : delete h ⟨⟨m + 1, hm⟩, e⟩ u =
          ⟨⟨m, Nat.lt_of_succ_lt hm⟩,
            Minimap.deleteMem (Nat.le_of_lt_succ hm) h e u hu⟩ := by
        unfold delete; simp only [hu, ↓reduceDIte]
      rw [hdel]
      exact Minimap.unusedSlotsZero_deleteMem (Nat.le_of_lt_succ hm) h e u hu
  · have hdel : delete h ⟨⟨m, hm⟩, e⟩ u = ⟨⟨m, hm⟩, e⟩ := by
      unfold delete; simp only [hu, ↓reduceDIte]
    rw [hdel]
    exact hz

end BoundedEncoded

/-- Canonical representation (history independence) of `Encoded`: for a fixed matching scheme `h`,
any two well-formed minimap states with zeroed unused slots that induce the same `query` map are
identical (`header` and `slots` agree bit-for-bit). -/
theorem eq_of_query_eq {U' n' X m : ℕ} (hm : m ≤ n')
    (h : DynamicMatching.Scheme U' n') {e₁ e₂ : Encoded U' n' X m}
    (hwf₁ : WellFormed hm h e₁) (hwf₂ : WellFormed hm h e₂)
    (hz₁ : UnusedSlotsZero h e₁) (hz₂ : UnusedSlotsZero h e₂)
    (hq : query h e₁ = query h e₂) : e₁ = e₂ := by
  have hqfin : ∀ u, queryFin h e₁ u = queryFin h e₂ u := fun u => by
    have hqu : (queryFin h e₁ u).map Fin.val = (queryFin h e₂ u).map Fin.val := congrFun hq u
    cases h1 : queryFin h e₁ u <;> cases h2 : queryFin h e₂ u
    · rfl
    · simp [h1, h2] at hqu
    · simp [h1, h2] at hqu
    · rename_i x₁ x₂
      simp only [h1, h2, Option.map_some, Option.some.injEq] at hqu
      exact congrArg some (Fin.ext hqu)
  have hmem_iff : ∀ {e : Encoded U' n' X m}, WellFormed hm h e →
      ∀ u, u ∈ activeSet e ↔ (queryFin h e u).isSome = true := fun {e} hwf u =>
    ⟨fun hu => (wellFormed_iff_queryFin_isSome hm h e).mp hwf u hu,
      fun his => by
        by_contra hnot
        rw [queryFin_of_notMem h e hnot] at his
        simp at his⟩
  have hact : activeSet e₁ = activeSet e₂ := by
    ext u
    rw [hmem_iff hwf₁ u, hmem_iff hwf₂ u, hqfin u]
  have hpairs : ∀ u (hu₁ : u ∈ activeSet e₁) (hu₂ : u ∈ activeSet e₂),
      unpackPair hm h e₁ hu₁ = unpackPair hm h e₂ hu₂ := fun u hu₁ hu₂ => by
    obtain ⟨x, hx₁⟩ := Option.isSome_iff_exists.mp ((hmem_iff hwf₁ u).mp hu₁)
    have hx₂ : queryFin h e₂ u = some x := (hqfin u).symm.trans hx₁
    rw [← decode?_unpackPair hm h e₁ hu₁, Spillover.decode?_eq_some_iff] at hx₁
    rw [← decode?_unpackPair hm h e₂ hu₂, Spillover.decode?_eq_some_iff] at hx₂
    exact hx₁.symm.trans hx₂
  have hhdr : e₁.header = e₂.header := by
    apply (headerEquiv U' m (Spillover.spillUniv X n')).symm.injective
    apply Prod.ext
    · exact Subtype.ext hact
    · funext i
      let u := (activeSet e₁).orderEmbOfFin (card_activeSet e₁) i
      have hu₁ : u ∈ activeSet e₁ := (activeSet e₁).orderEmbOfFin_mem (card_activeSet e₁) i
      have hu₂ : u ∈ activeSet e₂ := hact ▸ hu₁
      have hfst : spillOfMem e₁ hu₁ = spillOfMem e₂ hu₂ := by
        have hp := congrArg Prod.fst (hpairs u hu₁ hu₂)
        rwa [unpackPair_eq, unpackPair_eq] at hp
      have hidx₁ : ((activeSet e₁).orderIsoOfFin (card_activeSet e₁)).symm ⟨u, hu₁⟩ = i :=
        ((activeSet e₁).orderIsoOfFin (card_activeSet e₁)).symm_apply_apply i
      have hu_eq₂ : u = (activeSet e₂).orderEmbOfFin (card_activeSet e₂) i := by
        have hcongr : ∀ (S₁ S₂ : Finset (Fin U')) (h₁ : S₁.card = m) (h₂ : S₂.card = m),
            S₁ = S₂ → S₁.orderEmbOfFin h₁ i = S₂.orderEmbOfFin h₂ i := by
          rintro S _ h₁ h₂ rfl
          have hsub : h₁ = h₂ := Subsingleton.elim _ _
          subst hsub
          rfl
        exact hcongr _ _ _ _ hact
      have hsub₂ : (⟨u, hu₂⟩ : activeSet e₂) =
          (activeSet e₂).orderIsoOfFin (card_activeSet e₂) i := Subtype.ext hu_eq₂
      have hidx₂ : ((activeSet e₂).orderIsoOfFin (card_activeSet e₂)).symm ⟨u, hu₂⟩ = i := by
        rw [hsub₂, OrderIso.symm_apply_apply]
      dsimp only [spillOfMem, spillVec] at hfst
      rwa [hidx₁, hidx₂] at hfst
  have hslots : e₁.slots = e₂.slots := by
    funext b
    by_cases hex : ∃ a ∈ activeSet e₁, DynamicMatching.matchOpt h (activeSet e₁) a = some b
    · obtain ⟨a, ha₁, hab₁⟩ := hex
      have ha₂ : a ∈ activeSet e₂ := hact ▸ ha₁
      have hab₂ : DynamicMatching.matchOpt h (activeSet e₂) a = some b := hact ▸ hab₁
      rw [← unpackPair_snd_of_matchOpt hm h e₁ ha₁ hab₁,
        ← unpackPair_snd_of_matchOpt hm h e₂ ha₂ hab₂,
        congrArg Prod.snd (hpairs a ha₁ ha₂)]
    · push Not at hex
      have hex₂ : ∀ a ∈ activeSet e₂, DynamicMatching.matchOpt h (activeSet e₂) a ≠ some b :=
        hact ▸ hex
      rw [hz₁ b hex, hz₂ b hex₂]
  cases e₁
  cases e₂
  dsimp only at hhdr hslots
  rw [hhdr, hslots]

/-- Canonicality of well-formed full-capacity leaf states `FixedEncoded U' n' X` (`m = n'`),
without an explicit `UnusedSlotsZero` hypothesis. -/
theorem eq_of_query_eq_fixed {U' n' X : ℕ}
    (h : DynamicMatching.Scheme U' n') {e₁ e₂ : FixedEncoded U' n' X}
    (hwf₁ : WellFormed le_rfl h e₁) (hwf₂ : WellFormed le_rfl h e₂)
    (hq : query h e₁ = query h e₂) : e₁ = e₂ :=
  eq_of_query_eq le_rfl h hwf₁ hwf₂ (unusedSlotsZero_fixed h e₁)
    (unusedSlotsZero_fixed h e₂) hq

private theorem slotDiff_packPairs_le {U' n' X m m' : ℕ} (hm : m ≤ n')
    (hm' : m' ≤ n') (h : DynamicMatching.Scheme U' n') (e : Encoded U' n' X m)
    (hz : UnusedSlotsZero h e) (S' : Finset (Fin U')) (hS' : S'.card = m')
    (pairs' : (a : Fin U') → a ∈ S' →
      Fin (Spillover.spillUniv X n') × Fin (2 ^ Spillover.memBits X n'))
    (V : Finset (Fin U'))
    (hsame : ∀ a (ha : a ∈ activeSet e) (ha' : a ∈ S'),
      a ∉ V → pairs' a ha' = unpackPair hm h e ha) :
    slotDiff e (packPairs hm' h S' hS' pairs') ≤
      2 * ((Finset.univ.filter fun a =>
        DynamicMatching.matchOpt h (activeSet e) a ≠
          DynamicMatching.matchOpt h S' a) ∪ V).card := by
  set S := activeSet e
  set D := Finset.univ.filter fun a =>
    DynamicMatching.matchOpt h S a ≠ DynamicMatching.matchOpt h S' a
  set T := (D ∪ V).biUnion fun a =>
    (DynamicMatching.matchOpt h S a).toFinset ∪ (DynamicMatching.matchOpt h S' a).toFinset
  have hsub : (Finset.univ.filter fun b : Fin n' =>
      e.slots b ≠ (packPairs hm' h S' hS' pairs').slots b) ⊆ T := by
    intro b hb
    have hneq : e.slots b ≠ (packPairs hm' h S' hS' pairs').slots b := (mem_filter.mp hb).2
    by_contra hnotT
    apply hneq
    by_cases hex' : ∃ a', DynamicMatching.matchOpt h S' a' = some b
    · obtain ⟨a', hab'⟩ := hex'
      have ha_not : a' ∉ D ∪ V := fun hm =>
        hnotT (mem_biUnion.mpr ⟨a', hm, mem_union_right _ (by simp [hab'])⟩)
      have ha_notD : a' ∉ D := fun hm => ha_not (mem_union_left _ hm)
      have ha_notV : a' ∉ V := fun hm => ha_not (mem_union_right _ hm)
      have heq_m : DynamicMatching.matchOpt h S a' = some b := by
        have h1 : ¬ (DynamicMatching.matchOpt h S a' ≠ DynamicMatching.matchOpt h S' a') :=
          fun hne => ha_notD (mem_filter.mpr ⟨mem_univ a', hne⟩)
        rw [Classical.not_not.mp h1, hab']
      have hSle : S.card ≤ n' := (card_activeSet e).le.trans hm
      have haS : a' ∈ S := (DynamicMatching.matchOpt_isSome_iff h hSle a').mp (by rw [heq_m]; rfl)
      obtain ⟨haS', hslot'⟩ := slots_packPairs_of_matchOpt hm' h S' hS' pairs' hab'
      rw [hslot', hsame a' haS haS' ha_notV, unpackPair_snd_of_matchOpt hm h e haS heq_m]
    · push Not at hex'
      have hslot' : (packPairs hm' h S' hS' pairs').slots b = ⟨0, Nat.two_pow_pos _⟩ :=
        slots_packPairs_of_forall_ne hm' h S' hS' pairs' fun a' _ => hex' a'
      have hnoneS : ∀ a ∈ S, DynamicMatching.matchOpt h S a ≠ some b := by
        intro a _ hab
        have hne_m : DynamicMatching.matchOpt h S a ≠ DynamicMatching.matchOpt h S' a := by
          rw [hab]; exact (hex' a).symm
        exact hnotT (mem_biUnion.mpr ⟨a, mem_union_left _ (mem_filter.mpr ⟨mem_univ a, hne_m⟩),
          mem_union_left _ (by simp [hab])⟩)
      rw [hslot', hz b hnoneS]
  calc slotDiff e (packPairs hm' h S' hS' pairs')
      ≤ T.card := card_le_card hsub
    _ ≤ ∑ a ∈ D ∪ V,
          ((DynamicMatching.matchOpt h S a).toFinset ∪
            (DynamicMatching.matchOpt h S' a).toFinset).card := card_biUnion_le
    _ ≤ ∑ _a ∈ D ∪ V, 2 := sum_le_sum fun a _ => by
          have hc1 : (DynamicMatching.matchOpt h S a).toFinset.card ≤ 1 := by
            cases DynamicMatching.matchOpt h S a <;> simp
          have hc2 : (DynamicMatching.matchOpt h S' a).toFinset.card ≤ 1 := by
            cases DynamicMatching.matchOpt h S' a <;> simp
          exact (card_union_le _ _).trans (Nat.add_le_add hc1 hc2)
    _ = 2 * (D ∪ V).card := by simp [Nat.mul_comm]

/-- Deterministic `O(T)` slot-relocation bound for inserting a fresh key (`Lemma 3.7` and
`Lemma 3.2`): `slotDiff ≤ 4 * (rounds h (activeSet e) + 1)`. -/
theorem slotDiff_insertNew_le {U' n' X m : ℕ} (hm' : m + 1 ≤ n')
    (h : DynamicMatching.Scheme U' n') (e : Encoded U' n' X m) (hz : UnusedSlotsZero h e)
    (u : Fin U') (v : ℕ) (hv : v < X) (hu : u ∉ activeSet e) :
    slotDiff e (insertNew hm' h e u v hv hu) ≤
      4 * (DynamicMatching.rounds h (activeSet e) + 1) := by
  have hm : m ≤ n' := Nat.le_of_succ_le hm'
  have hSle : (activeSet e).card ≤ n' := (card_activeSet e).le.trans hm
  have hins_le : (insert u (activeSet e)).card ≤ n' := by
    rw [card_insert_of_notMem hu, card_activeSet]; exact hm'
  dsimp only [insertNew]
  refine (slotDiff_packPairs_le hm hm' h e hz (insert u (activeSet e)) _ _ {u} ?_).trans ?_
  · intro a ha _ haV
    have hau : a ≠ u := fun heq => haV (mem_singleton.mpr heq)
    simp [hau]
  · have hu_memD : u ∈ Finset.univ.filter (fun a =>
        DynamicMatching.matchOpt h (activeSet e) a ≠
          DynamicMatching.matchOpt h (insert u (activeSet e)) a) := by
      refine mem_filter.mpr ⟨mem_univ u, fun heq => ?_⟩
      have his1 : (DynamicMatching.matchOpt h (activeSet e) u).isSome = false := by
        rw [Bool.eq_false_iff]
        exact fun hm_some =>
          hu ((DynamicMatching.matchOpt_isSome_iff h hSle u).mp hm_some)
      have his2 : (DynamicMatching.matchOpt h (insert u (activeSet e)) u).isSome = true :=
        (DynamicMatching.matchOpt_isSome_iff h hins_le u).mpr
          (mem_insert_self u _)
      rw [heq, his2] at his1
      exact Bool.false_ne_true his1.symm
    have hunion : ((Finset.univ.filter fun a =>
        DynamicMatching.matchOpt h (activeSet e) a ≠
          DynamicMatching.matchOpt h (insert u (activeSet e)) a) ∪ {u}) =
        (Finset.univ.filter fun a =>
          DynamicMatching.matchOpt h (activeSet e) a ≠
            DynamicMatching.matchOpt h (insert u (activeSet e)) a) :=
      union_eq_left.mpr (singleton_subset_iff.mpr hu_memD)
    rw [hunion]
    have hrel := DynamicMatching.relocDist_insert_le h u hins_le
    dsimp only [DynamicMatching.relocDist] at hrel
    omega

/-- Overwriting an existing key's value changes at most `2` slots (in fact only its own slot). -/
theorem slotDiff_overwrite_le {U' n' X m : ℕ} (hm : m ≤ n')
    (h : DynamicMatching.Scheme U' n') (e : Encoded U' n' X m) (hz : UnusedSlotsZero h e)
    (u : Fin U') (v : ℕ) (hv : v < X) (hu : u ∈ activeSet e) :
    slotDiff e (overwrite hm h e u v hv hu) ≤ 2 := by
  dsimp only [overwrite]
  refine (slotDiff_packPairs_le hm hm h e hz (activeSet e) (card_activeSet e) _ {u} ?_).trans ?_
  · intro a _ _ haV
    have hau : a ≠ u := fun heq => haV (mem_singleton.mpr heq)
    simp [hau]
  · have hemp : (Finset.univ.filter fun a =>
        DynamicMatching.matchOpt h (activeSet e) a ≠
          DynamicMatching.matchOpt h (activeSet e) a) = ∅ := by simp
    rw [hemp]
    simp

/-- Deterministic `O(T)` slot-relocation bound for deleting an active key:
`slotDiff ≤ 4 * (rounds h (activeSet e) + 1)`. -/
theorem slotDiff_deleteMem_le {U' n' X m : ℕ} (hm' : m + 1 ≤ n')
    (h : DynamicMatching.Scheme U' n') (e : Encoded U' n' X (m + 1)) (hz : UnusedSlotsZero h e)
    (u : Fin U') (hu : u ∈ activeSet e) :
    slotDiff e (deleteMem hm' h e u hu) ≤
      4 * (DynamicMatching.rounds h (activeSet e) + 1) := by
  have hSle : (activeSet e).card ≤ n' := (card_activeSet e).le.trans hm'
  dsimp only [deleteMem]
  refine (slotDiff_packPairs_le hm' (Nat.le_of_succ_le hm') h e hz
    ((activeSet e).erase u) _ _ ∅ (fun _ _ _ _ => rfl)).trans ?_
  rw [union_empty]
  have hrel := DynamicMatching.relocDist_delete_le h u hSle
  dsimp only [DynamicMatching.relocDist] at hrel
  omega

/-- Deterministic `O(T)` slot-relocation bound for atomic leaf replacement on `FixedEncoded`
(requires **no** `UnusedSlotsZero` hypothesis, since `unusedSlotsZero_fixed` holds automatically):
`slotDiff ≤ 8 * rounds h (activeSet e) + 14`. -/
theorem slotDiff_replace_le {U' n' X : ℕ} (h : DynamicMatching.Scheme U' n')
    (e : FixedEncoded U' n' X) (x_old x_new : Fin U') (v_new : ℕ) (hv : v_new < X)
    (hx_old : x_old ∈ activeSet e) (hx_new : x_new ∉ (activeSet e).erase x_old) :
    slotDiff e (replace h e x_old x_new v_new hv hx_old hx_new) ≤
      8 * DynamicMatching.rounds h (activeSet e) + 14 := by
  have hz := unusedSlotsZero_fixed h e
  have hSle : (activeSet e).card ≤ n' := (card_activeSet e).le
  have hrep_le : (insert x_new ((activeSet e).erase x_old)).card ≤ n' := by
    have hpos : 1 ≤ n' := by
      have hc : 0 < (activeSet e).card := card_pos.mpr ⟨x_old, hx_old⟩
      rw [card_activeSet] at hc; exact hc
    rw [card_insert_of_notMem hx_new, card_erase_of_mem hx_old, card_activeSet]
    omega
  dsimp only [replace]
  refine (slotDiff_packPairs_le le_rfl le_rfl h e hz
    (insert x_new ((activeSet e).erase x_old)) _ _ {x_new} ?_).trans ?_
  · intro a _ _ haV
    have han : a ≠ x_new := fun heq => haV (mem_singleton.mpr heq)
    simp [han]
  · have hunion_le : ((Finset.univ.filter fun a =>
        DynamicMatching.matchOpt h (activeSet e) a ≠
          DynamicMatching.matchOpt h (insert x_new ((activeSet e).erase x_old)) a) ∪
        {x_new}).card ≤
        DynamicMatching.relocDist (DynamicMatching.matchOpt h (activeSet e))
          (DynamicMatching.matchOpt h (insert x_new ((activeSet e).erase x_old))) + 1 :=
      (card_union_le _ _).trans (by simp [DynamicMatching.relocDist])
    have hrel := DynamicMatching.relocDist_replace_le h x_old x_new hSle hrep_le
    omega

/-- Expected `O(log (max n' 2))` slot-relocation bound for fresh-key insertion (`Lemma 3.7`) across
any scheme-indexed family `e` with fixed active key set `S`. -/
theorem expect_slotDiff_insertNew_le {U' n' X m : ℕ} (hm' : m + 1 ≤ n')
    {S : Finset (Fin U')} (e : DynamicMatching.Scheme U' n' → Encoded U' n' X m)
    (hact : ∀ h, activeSet (e h) = S) (hz : ∀ h, UnusedSlotsZero h (e h))
    (u : Fin U') (v : ℕ) (hv : v < X) (hu : ∀ h, u ∉ activeSet (e h)) :
    (∑ h : DynamicMatching.Scheme U' n',
      (DynamicMatching.schemePMF U' n' h).toReal *
        (slotDiff (e h) (insertNew hm' h (e h) u v hv (hu h)) : ℝ)) ≤
      16 * (Nat.clog 2 (max n' 2) : ℝ) := by
  have hm : m ≤ n' := Nat.le_of_succ_le hm'
  have hS_card : S.card = m := by
    have h0 := card_activeSet (e fun _ => Equiv.refl _)
    rwa [hact] at h0
  have hSle : S.card ≤ n' := hS_card.le.trans hm
  have hpt : ∀ h : DynamicMatching.Scheme U' n',
      (slotDiff (e h) (insertNew hm' h (e h) u v hv (hu h)) : ℝ) ≤
        4 + 4 * (DynamicMatching.rounds h S : ℝ) := by
    intro h
    have hnat := slotDiff_insertNew_le hm' h (e h) (hz h) u v hv (hu h)
    rw [hact h] at hnat
    have hR : (slotDiff (e h) (insertNew hm' h (e h) u v hv (hu h)) : ℝ) ≤
        ((4 * (DynamicMatching.rounds h S + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
    push_cast at hR
    linarith
  have h1 := Cslib.Probability.PMF.sum_le_affine (DynamicMatching.schemePMF U' n') hpt
  have h2 := DynamicMatching.expect_rounds_le (U' := U') hSle
  have hclog_mono : (Nat.clog 2 (max S.card 2) : ℝ) ≤ Nat.clog 2 (max n' 2) := by
    exact_mod_cast Nat.clog_mono_right 2 (max_le_max_right 2 hSle)
  have hclog1 : (1 : ℝ) ≤ Nat.clog 2 (max n' 2) := by
    exact_mod_cast (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mpr (by simp : 2 ^ 0 < max n' 2)
  linarith

/-- Expected `O(log (max n' 2))` slot-relocation bound for inserting a fresh key `(u, v)` into the
canonical encoding `encode _ h s hb hs` of any fixed dictionary `s` (`Lemma 3.7`). -/
theorem expect_slotDiff_insertNew_encode_le {U' n' X m : ℕ} (hm' : m + 1 ≤ n')
    (s : Dictionary.State U') (hb : Dictionary.ValuesBounded X s)
    (hs : (Dictionary.dom s).card = m) (u : Fin U') (v : ℕ) (hv : v < X)
    (hu : u ∉ Dictionary.dom s) :
    (∑ h : DynamicMatching.Scheme U' n',
      (DynamicMatching.schemePMF U' n' h).toReal *
        (slotDiff (encode (Nat.le_of_succ_le hm') h s hb hs)
          (insertNew hm' h (encode (Nat.le_of_succ_le hm') h s hb hs) u v hv
            (by rwa [activeSet_encode])) : ℝ)) ≤
      16 * (Nat.clog 2 (max n' 2) : ℝ) :=
  expect_slotDiff_insertNew_le hm'
    (fun h => encode (Nat.le_of_succ_le hm') h s hb hs)
    (fun h => activeSet_encode (Nat.le_of_succ_le hm') h s hb hs)
    (fun h => unusedSlotsZero_encode (Nat.le_of_succ_le hm') h s hb hs)
    u v hv (fun _ => by rwa [activeSet_encode])

/-- Expected `O(log (max n' 2))` slot-relocation bound for active-key deletion (`Lemma 3.7`) across
any scheme-indexed family `e` with fixed active key set `S`. -/
theorem expect_slotDiff_deleteMem_le {U' n' X m : ℕ} (hm' : m + 1 ≤ n')
    {S : Finset (Fin U')} (e : DynamicMatching.Scheme U' n' → Encoded U' n' X (m + 1))
    (hact : ∀ h, activeSet (e h) = S) (hz : ∀ h, UnusedSlotsZero h (e h))
    (u : Fin U') (hu : ∀ h, u ∈ activeSet (e h)) :
    (∑ h : DynamicMatching.Scheme U' n',
      (DynamicMatching.schemePMF U' n' h).toReal *
        (slotDiff (e h) (deleteMem hm' h (e h) u (hu h)) : ℝ)) ≤
      16 * (Nat.clog 2 (max n' 2) : ℝ) := by
  have hS_card : S.card = m + 1 := by
    have h0 := card_activeSet (e fun _ => Equiv.refl _)
    rwa [hact] at h0
  have hSle : S.card ≤ n' := hS_card.le.trans hm'
  have hpt : ∀ h : DynamicMatching.Scheme U' n',
      (slotDiff (e h) (deleteMem hm' h (e h) u (hu h)) : ℝ) ≤
        4 + 4 * (DynamicMatching.rounds h S : ℝ) := by
    intro h
    have hnat := slotDiff_deleteMem_le hm' h (e h) (hz h) u (hu h)
    rw [hact h] at hnat
    have hR : (slotDiff (e h) (deleteMem hm' h (e h) u (hu h)) : ℝ) ≤
        ((4 * (DynamicMatching.rounds h S + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
    push_cast at hR
    linarith
  have h1 := Cslib.Probability.PMF.sum_le_affine (DynamicMatching.schemePMF U' n') hpt
  have h2 := DynamicMatching.expect_rounds_le (U' := U') hSle
  have hclog_mono : (Nat.clog 2 (max S.card 2) : ℝ) ≤ Nat.clog 2 (max n' 2) := by
    exact_mod_cast Nat.clog_mono_right 2 (max_le_max_right 2 hSle)
  have hclog1 : (1 : ℝ) ≤ Nat.clog 2 (max n' 2) := by
    exact_mod_cast (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mpr (by simp : 2 ^ 0 < max n' 2)
  linarith

/-- Expected `O(log (max n' 2))` slot-relocation bound for deleting an active key `u` from the
canonical encoding `encode hm' h s hb hs` of any fixed dictionary `s` (`Lemma 3.7`). -/
theorem expect_slotDiff_deleteMem_encode_le {U' n' X m : ℕ} (hm' : m + 1 ≤ n')
    (s : Dictionary.State U') (hb : Dictionary.ValuesBounded X s)
    (hs : (Dictionary.dom s).card = m + 1) (u : Fin U') (hu : u ∈ Dictionary.dom s) :
    (∑ h : DynamicMatching.Scheme U' n',
      (DynamicMatching.schemePMF U' n' h).toReal *
        (slotDiff (encode hm' h s hb hs)
          (deleteMem hm' h (encode hm' h s hb hs) u (by rwa [activeSet_encode])) : ℝ)) ≤
      16 * (Nat.clog 2 (max n' 2) : ℝ) :=
  expect_slotDiff_deleteMem_le hm'
    (fun h => encode hm' h s hb hs)
    (fun h => activeSet_encode hm' h s hb hs)
    (fun h => unusedSlotsZero_encode hm' h s hb hs)
    u (fun _ => by rwa [activeSet_encode])

/-- Expected `O(log (max n' 2))` slot-relocation bound for atomic leaf replacement (`Section 5.2`)
across any scheme-indexed full-capacity family `e` with fixed active key set `S`. -/
theorem expect_slotDiff_replace_le {U' n' X : ℕ}
    {S : Finset (Fin U')} (e : DynamicMatching.Scheme U' n' → FixedEncoded U' n' X)
    (hact : ∀ h, activeSet (e h) = S) (x_old x_new : Fin U') (v_new : ℕ) (hv : v_new < X)
    (hx_old : ∀ h, x_old ∈ activeSet (e h))
    (hx_new : ∀ h, x_new ∉ (activeSet (e h)).erase x_old) :
    (∑ h : DynamicMatching.Scheme U' n',
      (DynamicMatching.schemePMF U' n' h).toReal *
        (slotDiff (e h)
          (replace h (e h) x_old x_new v_new hv (hx_old h) (hx_new h)) : ℝ)) ≤
      38 * (Nat.clog 2 (max n' 2) : ℝ) := by
  have hS_card : S.card = n' := by
    have h0 := card_activeSet (e fun _ => Equiv.refl _)
    rwa [hact] at h0
  have hSle : S.card ≤ n' := hS_card.le
  have hpt : ∀ h : DynamicMatching.Scheme U' n',
      (slotDiff (e h)
        (replace h (e h) x_old x_new v_new hv (hx_old h) (hx_new h)) : ℝ) ≤
        14 + 8 * (DynamicMatching.rounds h S : ℝ) := by
    intro h
    have hnat := slotDiff_replace_le h (e h) x_old x_new v_new hv (hx_old h) (hx_new h)
    rw [hact h] at hnat
    have hR : (slotDiff (e h)
        (replace h (e h) x_old x_new v_new hv (hx_old h) (hx_new h)) : ℝ) ≤
        ((8 * DynamicMatching.rounds h S + 14 : ℕ) : ℝ) := by exact_mod_cast hnat
    push_cast at hR
    linarith
  have h1 := Cslib.Probability.PMF.sum_le_affine (DynamicMatching.schemePMF U' n') hpt
  have h2 := DynamicMatching.expect_rounds_le (U' := U') hSle
  have hclog_eq : max S.card 2 = max n' 2 := by rw [hS_card]
  rw [hclog_eq] at h2
  have hclog1 : (1 : ℝ) ≤ Nat.clog 2 (max n' 2) := by
    exact_mod_cast (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mpr (by simp : 2 ^ 0 < max n' 2)
  linarith

/-- Expected `O(log (max n' 2))` slot-relocation bound for atomic leaf replacement (`Section 5.2`)
on the canonical encoding `encode le_rfl h s hb hs` of any fixed `n'`-key dictionary `s`. -/
theorem expect_slotDiff_replace_encode_le {U' n' X : ℕ}
    (s : Dictionary.State U') (hb : Dictionary.ValuesBounded X s)
    (hs : (Dictionary.dom s).card = n') (x_old x_new : Fin U') (v_new : ℕ) (hv : v_new < X)
    (hx_old : x_old ∈ Dictionary.dom s) (hx_new : x_new ∉ (Dictionary.dom s).erase x_old) :
    (∑ h : DynamicMatching.Scheme U' n',
      (DynamicMatching.schemePMF U' n' h).toReal *
        (slotDiff (encode le_rfl h s hb hs)
          (replace h (encode le_rfl h s hb hs) x_old x_new v_new hv
            (by rwa [activeSet_encode]) (by rwa [activeSet_encode])) : ℝ)) ≤
      38 * (Nat.clog 2 (max n' 2) : ℝ) :=
  expect_slotDiff_replace_le
    (fun h => encode le_rfl h s hb hs)
    (fun h => activeSet_encode le_rfl h s hb hs)
    x_old x_new v_new hv
    (fun _ => by rwa [activeSet_encode])
    (fun _ => by rwa [activeSet_encode])

end Cslib.DataStructure.Dictionary.Minimap
