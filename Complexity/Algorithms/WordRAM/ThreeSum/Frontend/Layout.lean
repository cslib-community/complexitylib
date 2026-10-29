/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Frontend.Model
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Native frontend descriptor layout

Descriptors have six words, three consecutive `(length,pointer)` pairs. Arrays occupy
disjoint blocks of capacity `n+1`; unused capacity is outside the compact enumeration.
The first four `n`-word blocks remain reserved for radix sorting and full multiplicities.

## Main definitions

* `Layout`: concrete descriptor and payload addresses.
* `array`: the compact list represented by one array slot.
* `Output`: exact descriptor words and payload readback, including empty arrays.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Frontend

open Cslib.WordRAM

/-- Concrete layout at input length `n` and runtime label-bit budget `Λ`. -/
structure Layout where
  /-- Input length. -/
  n : ℕ
  /-- Number of label bits. -/
  digits : ℕ

namespace Layout

/-- Number of bit-split triples. -/
def splits (l : Layout) : ℕ := 2 * l.digits ^ 2
/-- Total descriptor count, including the two multiplicity triples. -/
def count (l : Layout) : ℕ := l.splits + 2
/-- Total compact array count. -/
def arrays (l : Layout) : ℕ := 3 * l.count
/-- Capacity allows singleton zero even when the original input is empty. -/
def capacity (l : Layout) : ℕ := l.n + 1
/-- Descriptor table follows all four radix buffers. -/
def descriptors (l : Layout) : ℕ := 1 + 4 * l.n
/-- Payload blocks follow the complete descriptor table. -/
def payloads (l : Layout) : ℕ := l.descriptors + 2 * l.arrays
/-- Pointer for array slot `j`. -/
def pointer (l : Layout) (j : ℕ) : ℕ := l.payloads + l.capacity * j
/-- One-past-end address of all allocated blocks. -/
def endpoint (l : Layout) : ℕ := l.pointer l.arrays

/-- Payload pointers advance by the full reserved capacity. -/
theorem pointer_succ (l : Layout) (j : ℕ) : l.pointer (j + 1) = l.pointer j + l.capacity := by
  simp only [pointer, Nat.mul_add, Nat.mul_one, Nat.add_assoc]

/-- Payload blocks occur in allocation order. -/
theorem pointer_mono (l : Layout) {i j : ℕ} (h : i ≤ j) : l.pointer i ≤ l.pointer j :=
  Nat.add_le_add_left (Nat.mul_le_mul_left _ h) _

/-- Every descriptor word precedes every payload block. -/
theorem descriptor_before (l : Layout) {j : ℕ} (hj : j < l.arrays) (i : ℕ) :
    l.descriptors + 2 * j + 2 ≤ l.pointer i := by
  dsimp only [pointer, payloads]
  omega

end Layout

namespace Math

/-- Selection mode for a physical array slot. -/
def mode (Λ j : ℕ) : ℕ :=
  let t := j / 3
  let s := j % 3
  if t < 2 * Λ ^ 2 then s
  else if t = 2 * Λ ^ 2 then if s = 0 then 3 else if s = 1 then 6 else 5
  else if s = 0 then 4 else 6

/-- Bit coordinates of a physical slot in the split part of the table. -/
def beta (Λ j : ℕ) : ℕ := (j / 3 / 2) / Λ
@[inherit_doc beta] def beta' (Λ j : ℕ) : ℕ := (j / 3 / 2) % Λ
@[inherit_doc beta] def digit (j : ℕ) : ℕ := j / 3 % 2

/-- Compact encoded list for one physical array slot. -/
def array (U Λ : ℕ) (rs : List (ℕ × ℕ)) (j : ℕ) : List ℕ :=
  if mode Λ j = 6 then [0]
  else select U (beta Λ j) (beta' Λ j) (digit j) (mode Λ j) rs

/-- The two bit coordinates are irrelevant in the three nonsplitting scan modes. -/
theorem select_extra (U β β' v mode : ℕ) (rs : List (ℕ × ℕ)) (hm : 3 ≤ mode) :
    select U β β' v mode rs = select U 0 0 0 mode rs := by
  unfold select
  congr 2
  funext p
  unfold keep flag
  split <;> first | rfl | omega

/-- Physical array slots within a split triple follow A, B₀, B₁ order. -/
theorem array_split (U Λ : ℕ) (rs : List (ℕ × ℕ)) (t s : ℕ)
    (ht : t < 2 * Λ ^ 2) (hs : s < 3) :
    array U Λ rs (3 * t + s) = select U (t / 2 / Λ) (t / 2 % Λ) (t % 2) s rs := by
  have hd : (3 * t + s) / 3 = t := by omega
  have hm : (3 * t + s) % 3 = s := by omega
  have hn : s ≠ 6 := by omega
  simp [array, mode, hd, hm, ht, hn, beta, beta', digit]

/-- Read the three array specifications belonging to a descriptor. -/
def root (U Λ : ℕ) (rs : List (ℕ × ℕ)) (t : ℕ) : List ℕ × List ℕ × List ℕ :=
  (array U Λ rs (3 * t), array U Λ rs (3 * t + 1), array U Λ rs (3 * t + 2))

/-- A descriptor in the split prefix has exactly the requested three compact selections. -/
theorem root_split (U Λ : ℕ) (rs : List (ℕ × ℕ)) (t : ℕ) (ht : t < 2 * Λ ^ 2) :
    root U Λ rs t =
      (select U (t / 2 / Λ) (t / 2 % Λ) (t % 2) 0 rs,
        select U (t / 2 / Λ) (t / 2 % Λ) (t % 2) 1 rs,
        select U (t / 2 / Λ) (t / 2 % Λ) (t % 2) 2 rs) := by
  have h0 := array_split U Λ rs t 0 ht (by decide)
  simp only [Nat.add_zero] at h0
  simp only [root, h0, array_split U Λ rs t 1 ht (by decide),
    array_split U Λ rs t 2 ht (by decide)]

/-- The two final descriptors retain their singleton zeros and exact multiplicity scans. -/
theorem root_extras (U Λ : ℕ) (rs : List (ℕ × ℕ)) :
    root U Λ rs (2 * Λ ^ 2) =
      (select U 0 0 0 3 rs, [0], select U 0 0 0 5 rs) ∧
    root U Λ rs (2 * Λ ^ 2 + 1) = (select U 0 0 0 4 rs, [0], [0]) := by
  constructor
  all_goals simp [root, array, mode, select_extra, Nat.add_div, Nat.add_mod,
    show ∀ n, ¬n + 1 < n from fun _ => by omega]

/-- Every array fits in its `n+1` capacity, including empty-input singleton zeros. -/
theorem length_array_le (U Λ : ℕ) (rs : List (ℕ × ℕ)) (j : ℕ) :
    (array U Λ rs j).length ≤ rs.length + 1 := by
  dsimp only [array]
  split_ifs
  · simp
  · exact (length_select_le _ _ _ _ _ _).trans (by omega)

/-- Every descriptor represents an injective enumeration. -/
theorem array_nodup (U Λ : ℕ) {rs : List (ℕ × ℕ)}
    (h : (rs.map Prod.fst).Nodup) (j : ℕ) : (array U Λ rs j).Nodup := by
  dsimp only [array]
  split_ifs
  · simp
  · exact select_nodup _ _ _ _ _ h

/-- Each output word is canonical zero, an original input key, or the key of twice an input. -/
theorem array_values {input : List ℤ} {rs : List (ℕ × ℕ)}
    (hkeys : ∀ k, k ∈ rs.map Prod.fst ↔ k ∈ input.map Signed.encode)
    (U Λ j u : ℕ) (hu : u ∈ array U Λ rs j) :
    u = 0 ∨ ∃ z ∈ input, u = Signed.encode z ∨ u = Signed.encode (2 * z) := by
  unfold array at hu
  split_ifs at hu
  · exact .inl (by simpa only [List.mem_singleton] using hu)
  · unfold select at hu
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hu
    obtain ⟨z, hz, he⟩ := List.mem_map.mp ((hkeys p.1).mp (List.mem_map.mpr
      ⟨p, (List.mem_filter.mp hp).1, rfl⟩))
    refine .inr ⟨z, hz, ?_⟩
    rw [← he]
    unfold value
    split_ifs
    · exact .inr (twice_encode z)
    · exact .inl rfl

/-- Every compact output word is a canonical signed encoding. -/
theorem array_canonical {input : List ℤ} {rs : List (ℕ × ℕ)}
    (hkeys : ∀ k, k ∈ rs.map Prod.fst ↔ k ∈ input.map Signed.encode)
    (U Λ j u : ℕ) (hu : u ∈ array U Λ rs j) : Signed.encode (Signed.decode u) = u := by
  rcases array_values hkeys U Λ j u hu with rfl | ⟨z, _, rfl | rfl⟩
  · rfl
  all_goals rw [Signed.decode_encode]

/-- Injectivity holds for the represented integer array, as well as its native keys. -/
theorem array_decoded_nodup {input : List ℤ} {rs : List (ℕ × ℕ)}
    (hkeys : ∀ k, k ∈ rs.map Prod.fst ↔ k ∈ input.map Signed.encode)
    (h : (rs.map Prod.fst).Nodup) (U Λ j : ℕ) :
    ((array U Λ rs j).map Signed.decode).Nodup := by
  apply List.Nodup.map_on _ (array_nodup U Λ h j)
  intro u hu v hv he
  rw [← array_canonical hkeys U Λ j u hu, ← array_canonical hkeys U Λ j v hv, he]

/-- Every decoded payload integer has the exact reduction's common magnitude bound `2U`. -/
theorem array_magnitude {input : List ℤ} {rs : List (ℕ × ℕ)} {U : ℕ}
    (hkeys : ∀ k, k ∈ rs.map Prod.fst ↔ k ∈ input.map Signed.encode)
    (hvalues : ∀ z ∈ input, |z| ≤ (U : ℤ)) (Λ j u : ℕ) (hu : u ∈ array U Λ rs j) :
    |Signed.decode u| ≤ (2 * U : ℕ) := by
  rcases array_values hkeys U Λ j u hu with rfl | ⟨z, hz, rfl | rfl⟩
  · simp [Signed.decode]
  · rw [Signed.decode_encode]
    have := hvalues z hz
    omega
  · rw [Signed.decode_encode]
    have := abs_le.mp (hvalues z hz)
    apply abs_le.mpr
    constructor <;> omega

/-- The compact root lists before their native layout is assigned. -/
def roots (U : ℕ) (rs : List (ℕ × ℕ)) : List (List ℕ × List ℕ × List ℕ) :=
  let Λ := Cslib.Algorithms.ThreeSum.labelBits (2 * U)
  ((List.range Λ).flatMap fun β => (List.range Λ).flatMap fun β' =>
    [false, true].map fun v =>
      (select U β β' v.toNat 0 rs, select U β β' v.toNat 1 rs,
        select U β β' v.toNat 2 rs)) ++
    [(select U 0 0 0 3 rs, [0], select U 0 0 0 5 rs),
      (select U 0 0 0 4 rs, [0], [0])]

/-- Decode a compact triple to the finite sets used by the existing reduction. -/
def decodeRoot (T : List ℕ × List ℕ × List ℕ) : Finset ℤ × Finset ℤ × Finset ℤ :=
  ((T.1.map Signed.decode).toFinset, (T.2.1.map Signed.decode).toFinset,
    (T.2.2.map Signed.decode).toFinset)

/-- Exact list equality with `ThreeSum.inputs`, preserving root order and every empty array. -/
theorem roots_decoded {input : List ℤ} {rs : List (ℕ × ℕ)} {U : ℕ}
    (hkeys : ∀ k, k ∈ rs.map Prod.fst ↔ k ∈ input.map Signed.encode)
    (hcounts : ∀ p ∈ rs, (input.map Signed.encode).count p.1 = p.2)
    (hvalues : ∀ z ∈ input, |z| ≤ (U : ℤ)) :
    (roots U rs).map decodeRoot =
      Cslib.Algorithms.ThreeSum.inputs U (fun i : Fin input.length => input[i]) := by
  simp only [roots, Cslib.Algorithms.ThreeSum.inputs, List.map_append, List.map_flatMap,
    decodeRoot, select_A hkeys hcounts hvalues,
    show ∀ β β' v, ((select U β β' v.toNat 1 rs).map Signed.decode).toFinset =
      Cslib.Algorithms.ThreeSum.splitB (2 * U) β β' v false
        (Finset.univ.image (fun i : Fin input.length => input[i]))
      from fun β β' v => select_B hkeys hcounts hvalues β β' v false,
    show ∀ β β' v, ((select U β β' v.toNat 2 rs).map Signed.decode).toFinset =
      Cslib.Algorithms.ThreeSum.splitB (2 * U) β β' v true
        (Finset.univ.image (fun i : Fin input.length => input[i]))
      from fun β β' v => select_B hkeys hcounts hvalues β β' v true,
    List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil,
    Signed.decode, Nat.zero_mod, ↓reduceIte, Nat.zero_div, Int.natCast_zero,
    Finset.insert_empty, select_twice hkeys hcounts, select_original hkeys hcounts,
    select_zero hkeys hcounts]

private theorem map_range_mul {α : Type*} (a b : ℕ) (f : ℕ → α) :
    (List.range (a * b)).map f =
      (List.range a).flatMap (fun i => (List.range b).map fun j => f (i * b + j)) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_mul, List.range_add, List.map_append, ih, List.range_succ,
      List.flatMap_append, List.flatMap_singleton]
    simp [List.map_map, Function.comp_def, Nat.add_comm]

/-- Physical descriptor indices have exactly the nested order of the finite root list. -/
theorem roots_indexed (U : ℕ) (rs : List (ℕ × ℕ)) :
    let Λ := Cslib.Algorithms.ThreeSum.labelBits (2 * U)
    (List.range (2 * Λ ^ 2 + 2)).map (root U Λ rs) = roots U rs := by
  dsimp only
  let Λ := Cslib.Algorithms.ThreeSum.labelBits (2 * U)
  have hΛ : 0 < Λ := by dsimp [Λ, Cslib.Algorithms.ThreeSum.labelBits]; omega
  have hlen : 2 * Λ ^ 2 = Λ * (Λ * 2) := by ring
  change (List.range (2 * Λ ^ 2 + 2)).map (root U Λ rs) = _
  rw [List.range_add, List.map_append]
  have hprefix : (List.range (2 * Λ ^ 2)).map (root U Λ rs) =
      (List.range Λ).flatMap (fun β => (List.range Λ).flatMap fun β' =>
        [false, true].map fun v =>
          (select U β β' v.toNat 0 rs, select U β β' v.toNat 1 rs,
            select U β β' v.toNat 2 rs)) := by
    rw [hlen, map_range_mul]
    apply List.flatMap_congr
    intro β hβ
    rw [map_range_mul]
    apply List.flatMap_congr
    intro β' hβ'
    have hb : β < Λ := List.mem_range.mp hβ
    have hb' : β' < Λ := List.mem_range.mp hβ'
    have hdiv : (β * Λ + β') / Λ = β := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hΛ, Nat.div_eq_of_lt hb', Nat.zero_add]
    have hmod : (β * Λ + β') % Λ = β' := Nat.mul_add_mod_of_lt hb'
    have hlt0 : β * (Λ * 2) + (β' * 2 + 0) < 2 * Λ ^ 2 := by nlinarith
    have hlt1 : β * (Λ * 2) + (β' * 2 + 1) < 2 * Λ ^ 2 := by nlinarith
    simp only [show List.range 2 = [0, 1] from rfl, List.map_cons, List.map_nil,
      root_split _ _ _ _ hlt0, root_split _ _ _ _ hlt1]
    have hmul : β * (Λ * 2) = 2 * (β * Λ) := by ring
    have hd0 : (β * (Λ * 2) + (β' * 2 + 0)) / 2 = β * Λ + β' := by rw [hmul]; omega
    have hd1 : (β * (Λ * 2) + (β' * 2 + 1)) / 2 = β * Λ + β' := by rw [hmul]; omega
    have hm0 : (β * (Λ * 2) + (β' * 2 + 0)) % 2 = 0 := by rw [hmul]; omega
    have hm1 : (β * (Λ * 2) + (β' * 2 + 1)) % 2 = 1 := by rw [hmul]; omega
    simp only [hd0, hd1, hm0, hm1, hdiv, hmod, Bool.toNat_false, Bool.toNat_true]
  rw [hprefix]
  simp only [show List.range 2 = [0, 1] from rfl, List.map_cons, List.map_nil,
    Nat.add_zero, (root_extras U Λ rs).1,
    (root_extras U Λ rs).2]
  rfl

end Math

/-- Exact descriptor and compact payload readback. Unused capacity is unrestricted. -/
def Output (l : Layout) (U : ℕ) (rs : List (ℕ × ℕ)) (mem : ℕ → ℕ) : Prop :=
  ∀ j < l.arrays,
    mem (l.descriptors + 2 * j) = (Math.array U l.digits rs j).length ∧
    mem (l.descriptors + 2 * j + 1) = l.pointer j ∧
    Block.HoldsList (l.pointer j) (Math.array U l.digits rs j) mem

/-- Follow one `(length,pointer)` pair in native memory. This is output interpretation,
not an instruction or an assumed computation by the frontend. -/
def readArray (mem : ℕ → ℕ) (a : ℕ) : List ℕ :=
  (List.range (mem a)).map fun i => mem (mem (a + 1) + i)

/-- Follow all six-word descriptors in order and decode their represented sets. -/
def readRoots (l : Layout) (mem : ℕ → ℕ) : List (Finset ℤ × Finset ℤ × Finset ℤ) :=
  (List.range l.count).map fun t =>
    let a := l.descriptors + 6 * t
    Math.decodeRoot (readArray mem a, readArray mem (a + 2), readArray mem (a + 4))

/-- Exact slot readback includes zero-length arrays and ignores unused capacity. -/
theorem Output.read_array {l : Layout} {U : ℕ} {rs : List (ℕ × ℕ)} {mem : ℕ → ℕ}
    (h : Output l U rs mem) {j : ℕ} (hj : j < l.arrays) :
    readArray mem (l.descriptors + 2 * j) = Math.array U l.digits rs j := by
  obtain ⟨hl, hp, hm⟩ := h j hj
  unfold readArray
  rw [hl, hp]
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simpa only [List.getElem_map, List.getElem_range] using hm.get i hi'

/-- The descriptor table reads back as exactly the existing finite frontend list, in order. -/
theorem Output.readback {n U : ℕ} {input : List ℤ} {rs : List (ℕ × ℕ)} {mem : ℕ → ℕ}
    (h : Output ⟨n, Cslib.Algorithms.ThreeSum.labelBits (2 * U)⟩ U rs mem)
    (hkeys : ∀ k, k ∈ rs.map Prod.fst ↔ k ∈ input.map Signed.encode)
    (hcounts : ∀ p ∈ rs, (input.map Signed.encode).count p.1 = p.2)
    (hvalues : ∀ z ∈ input, |z| ≤ (U : ℤ)) :
    readRoots ⟨n, Cslib.Algorithms.ThreeSum.labelBits (2 * U)⟩ mem =
      Cslib.Algorithms.ThreeSum.inputs U (fun i : Fin input.length => input[i]) := by
  let l : Layout := ⟨n, Cslib.Algorithms.ThreeSum.labelBits (2 * U)⟩
  have he : readRoots l mem =
      ((List.range l.count).map (Math.root U l.digits rs)).map Math.decodeRoot := by
    simp only [readRoots, List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro t ht
    have hti : t < l.count := List.mem_range.mp ht
    have hs (s : ℕ) (hs : s < 3) :
        readArray mem (l.descriptors + 6 * t + 2 * s) = Math.array U l.digits rs (3 * t + s) := by
      have hj : 3 * t + s < l.arrays := by dsimp only [Layout.arrays]; omega
      have ha : l.descriptors + 6 * t + 2 * s = l.descriptors + 2 * (3 * t + s) := by omega
      rw [ha]
      exact h.read_array hj
    have h0 := hs 0 (by decide)
    have h1 := hs 1 (by decide)
    have h2 := hs 2 (by decide)
    simpa only [Math.root, Nat.mul_zero, Nat.add_zero, Nat.mul_one] using
      congrArg Math.decodeRoot (congrArg₂ Prod.mk h0 (congrArg₂ Prod.mk h1 h2))
  rw [he]
  have hi := Math.roots_indexed U rs
  change (List.range l.count).map (Math.root U l.digits rs) = Math.roots U rs at hi
  rw [hi]
  exact Math.roots_decoded hkeys hcounts hvalues

end Cslib.Algorithms.WordRAM.ThreeSum.Frontend
