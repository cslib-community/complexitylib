/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.NodeLayout
public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.CountPlaceMemory

/-!
# Exact output memory of complete native Chan–He node construction

## Main definitions

* `NodePacking.paddingMemory`, `roundMemory`, `memory`: exact instruction-level write specs.
* `NodePacking.node`: the existing mathematical node for the three supplied enumerations.

## References

These memory composition proofs are original.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.NodePacking

open Cslib.WordRAM.Signed

/-- Every output cell is initialized, even when the three input arrays are empty. -/
def paddingMemory (L : Layout) (mem : ℕ → ℕ) : ℕ → ℕ :=
  Padding.memory mem L.packed (120 * L.U + 80) (16 * L.U + 10)
    (40 * L.U + 26) (44 * L.U + 30) L.N

/-- Exact complete count/place call for the selected supplied input array. -/
def roundMemory (L : Layout) (values : Fin 3 → ℕ → ℤ) (j : Fin 3) (mem : ℕ → ℕ) : ℕ → ℕ :=
  CountPlace.memory mem (values j) (L.n j) L.M (L.heavy j) L.packed (j.val + 1)
    (if j = 2 then 4 * L.M else 0) (L.tag j) L.scratch L.hist (L.descriptor j)
    (decide (j = 2))

/-- Exact memory after padding and all three complete native calls. -/
def memory (L : Layout) (values : Fin 3 → ℕ → ℤ) (mem : ℕ → ℕ) : ℕ → ℕ :=
  roundMemory L values 2 (roundMemory L values 1 (roundMemory L values 0 (paddingMemory L mem)))

/-- The existing mathematical Chan–He node, with no alternative 3SUM semantics. -/
def node (L : Layout) (values : Fin 3 → ℕ → ℤ) :
    Cslib.Algorithms.ThreeSum.ChanHe.Node :=
  ⟨(Finset.range (L.n 0)).image (values 0), (Finset.range (L.n 1)).image (values 1),
    (Finset.range (L.n 2)).image (values 2), L.M⟩

/-- The native unsigned pattern encodes exactly the signed padding and tags of `oneArray`. -/
theorem padding_values (L : Layout) :
    120 * L.U + 80 = encode (10 * (L.gap : ℤ)) ∧
      16 * L.U + 10 = encode (Cslib.Algorithms.ThreeSum.ChanHe.pad L.U + L.gap) ∧
      40 * L.U + 26 = encode (Cslib.Algorithms.ThreeSum.ChanHe.pad L.U + 3 * L.gap) ∧
      44 * L.U + 30 = encode (-Cslib.Algorithms.ThreeSum.ChanHe.pad L.U + 4 * L.gap) := by
  have h₀ : 10 * (L.gap : ℤ) = ((60 * L.U + 40 : ℕ) : ℤ) := by
    dsimp only [Layout.gap]
    push_cast
    ring
  have h₁ : Cslib.Algorithms.ThreeSum.ChanHe.pad L.U + (L.gap : ℤ) =
      ((8 * L.U + 5 : ℕ) : ℤ) := by
    dsimp only [Cslib.Algorithms.ThreeSum.ChanHe.pad, Layout.gap]
    push_cast
    ring
  have h₂ : Cslib.Algorithms.ThreeSum.ChanHe.pad L.U + 3 * (L.gap : ℤ) =
      ((20 * L.U + 13 : ℕ) : ℤ) := by
    dsimp only [Cslib.Algorithms.ThreeSum.ChanHe.pad, Layout.gap]
    push_cast
    ring
  have h₃ : -Cslib.Algorithms.ThreeSum.ChanHe.pad L.U + 4 * (L.gap : ℤ) =
      ((22 * L.U + 15 : ℕ) : ℤ) := by
    dsimp only [Cslib.Algorithms.ThreeSum.ChanHe.pad, Layout.gap]
    push_cast
    ring
  rw [h₀, h₁, h₂, h₃]
  simp only [encode, Int.natAbs_natCast, Int.natCast_nonneg, not_lt_of_ge,
    ↓reduceIte, Nat.add_zero]
  omega

/-- Reading initialized packed memory at any fitting index. -/
theorem paddingMemory_read (L : Layout) (mem : ℕ → ℕ) {u : ℕ} (hu : u < 4 * L.N) :
    paddingMemory L mem (L.packed + u) =
      Padding.pattern (120 * L.U + 80) (16 * L.U + 10) (40 * L.U + 26) (44 * L.U + 30) u := by
  simp [paddingMemory, Padding.memory, hu]

/-- Later rounds preserve every earlier count/capacity block. -/
theorem roundMemory_before (L : Layout) (values : Fin 3 → ℕ → ℤ) (j : Fin 3)
    (mem : ℕ → ℕ) (hM : 0 < L.M) (hN : 2 * L.M ≤ L.N)
    {a : ℕ} (ha : a < L.descriptor j) : roundMemory L values j mem a = mem a := by
  have ho := L.descriptor_lt_packed j
  apply CountPlace.memory_outside _ _ _ _ _ _ _ _ _ _ _ _ L.N _ hM hN
    (by omega) (by split_ifs <;> omega)
  · dsimp only [Layout.heavy]; omega
  · omega
  · dsimp only [Layout.scratch]; omega
  · dsimp only [Layout.hist, Layout.scratch]; omega
  · omega

/-- Every complete call preserves every other packed column, including column zero. -/
theorem roundMemory_other (L : Layout) (values : Fin 3 → ℕ → ℤ) (j : Fin 3)
    (mem : ℕ → ℕ) {u : ℕ} (hu : u < 4 * L.N) (hc : u % 4 ≠ j.val + 1) :
    roundMemory L values j mem (L.packed + u) = mem (L.packed + u) := by
  have hn := L.n_le_total j
  apply CountPlace.memory_other_column _ _ _ _ _ _ _ _ _ _ _ _ L.N _
    (L.heavy_end_le_packed j) (by omega)
    (by by_cases hj : j = 2 <;> simp [hj])
    le_rfl (Nat.add_le_add_left hn L.scratch) (L.descriptor_lt_packed j) hu hc

/-- The first two complete rounds produce the existing mathematical light array. -/
theorem roundMemory_arrXY (L : Layout) (values : Fin 3 → ℕ → ℤ) (j : Fin 3)
    (mem : ℕ → ℕ) (hj : j ≠ 2) (hM : 0 < L.M)
    (hinj : Set.InjOn (values j) (↑(Finset.range (L.n j)) : Set ℕ))
    {i : ℕ} (hi : i < L.N)
    (hpad : mem (L.packed + 4 * i + (j.val + 1)) =
      encode (Cslib.Algorithms.ThreeSum.ChanHe.pad L.U + L.tag j)) :
    roundMemory L values j mem (L.packed + 4 * i + (j.val + 1)) =
      encode (Cslib.Algorithms.ThreeSum.ChanHe.arrXY
        ((Finset.range (L.n j)).image (values j)) L.M L.U i + L.tag j) := by
  have hn := L.n_le_total j
  simpa only [roundMemory, hj, ↓reduceIte, decide_false] using
    CountPlace.memory_arrXY mem (values j) (L.n j) L.M (L.heavy j) L.packed (j.val + 1)
      (L.tag j) L.U L.scratch L.hist (L.descriptor j) L.N hM (L.heavy_end_le_packed j)
      le_rfl (Nat.add_le_add_left hn L.scratch) (L.descriptor_lt_packed j) hinj
      (by omega) hpad

/-- The third complete round produces the existing duplicated, negated mathematical array. -/
theorem roundMemory_arrZ (L : Layout) (values : Fin 3 → ℕ → ℤ)
    (mem : ℕ → ℕ) (hM : 0 < L.M)
    (hinj : Set.InjOn (values 2) (↑(Finset.range (L.n 2)) : Set ℕ))
    {i : ℕ} (hi : i < L.N)
    (hpad : mem (L.packed + 4 * i + 3) =
      encode (-Cslib.Algorithms.ThreeSum.ChanHe.pad L.U + 4 * L.gap)) :
    roundMemory L values 2 mem (L.packed + 4 * i + 3) =
      encode (Cslib.Algorithms.ThreeSum.ChanHe.arrZ
        ((Finset.range (L.n 2)).image (values 2)) L.M L.U i + 4 * L.gap) := by
  have hn := L.n_le_total 2
  simpa +decide only [roundMemory, Layout.tag, Nat.reduceAdd, ↓reduceIte,
    decide_true, Fin.val_two, Nat.cast_mul, Nat.cast_ofNat] using
    CountPlace.memory_arrZ mem (values 2) (L.n 2) L.M (L.heavy 2) L.packed 3
      (4 * L.gap) L.U L.scratch L.hist (L.descriptor 2) L.N hM (L.heavy_end_le_packed 2)
      le_rfl (Nat.add_le_add_left hn L.scratch) (L.descriptor_lt_packed 2) hinj
      (by omega) hpad

/-- All four packed columns have exactly the existing node's required values. -/
theorem memory_cells (L : Layout) (values : Fin 3 → ℕ → ℤ) (mem : ℕ → ℕ)
    (hM : 0 < L.M) (hinj : ∀ j, Set.InjOn (values j) (↑(Finset.range (L.n j)) : Set ℕ))
    {i : ℕ} (hi : i < L.N) :
    memory L values mem (L.packed + 4 * i) = encode (10 * (L.gap : ℤ)) ∧
      memory L values mem (L.packed + 4 * i + 1) = encode
        (Cslib.Algorithms.ThreeSum.ChanHe.arrXY (node L values).S₁ L.M L.U i + L.gap) ∧
      memory L values mem (L.packed + 4 * i + 2) = encode
        (Cslib.Algorithms.ThreeSum.ChanHe.arrXY (node L values).S₂ L.M L.U i + 3 * L.gap) ∧
      memory L values mem (L.packed + 4 * i + 3) = encode
        (Cslib.Algorithms.ThreeSum.ChanHe.arrZ (node L values).S₃ L.M L.U i + 4 * L.gap) := by
  have hp (c : ℕ) (hc : c < 4) :
      paddingMemory L mem (L.packed + (4 * i + c)) =
        Padding.pattern (120 * L.U + 80) (16 * L.U + 10)
          (40 * L.U + 26) (44 * L.U + 30) (4 * i + c) :=
    paddingMemory_read L mem (by omega)
  have hp₀ : paddingMemory L mem (L.packed + 4 * i) = encode (10 * (L.gap : ℤ)) := by
    have he := hp 0 (by decide)
    simpa [Padding.pattern, (padding_values L).1] using he
  have hp₁ : paddingMemory L mem (L.packed + 4 * i + 1) =
      encode (Cslib.Algorithms.ThreeSum.ChanHe.pad L.U + L.gap) := by
    have he := hp 1 (by decide)
    simpa [Padding.pattern, Nat.add_assoc, (padding_values L).2.1] using he
  have hp₂ : paddingMemory L mem (L.packed + 4 * i + 2) =
      encode (Cslib.Algorithms.ThreeSum.ChanHe.pad L.U + 3 * L.gap) := by
    have he := hp 2 (by decide)
    simpa [Padding.pattern, Nat.add_assoc, (padding_values L).2.2.1] using he
  have hp₃ : paddingMemory L mem (L.packed + 4 * i + 3) =
      encode (-Cslib.Algorithms.ThreeSum.ChanHe.pad L.U + 4 * L.gap) := by
    have he := hp 3 (by decide)
    simpa [Padding.pattern, Nat.add_assoc, (padding_values L).2.2.2] using he
  have other (j : Fin 3) (μ : ℕ → ℕ) (c : ℕ) (hc : c < 4) (hne : c ≠ j.val + 1) :
      roundMemory L values j μ (L.packed + 4 * i + c) = μ (L.packed + 4 * i + c) := by
    simpa only [Nat.add_assoc] using roundMemory_other L values j μ
      (u := 4 * i + c) (by omega) (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · change roundMemory L values 2 _ _ = _
    rw [show L.packed + 4 * i = L.packed + 4 * i + 0 by omega,
      other 2 _ 0 (by decide) (by decide), other 1 _ 0 (by decide) (by decide),
      other 0 _ 0 (by decide) (by decide)]
    exact hp₀
  · change roundMemory L values 2 _ _ = _
    rw [other 2 _ 1 (by decide) (by decide), other 1 _ 1 (by decide) (by decide)]
    simpa +decide [Layout.tag, node] using roundMemory_arrXY L values 0 (paddingMemory L mem)
      (by decide) hM (hinj 0) hi (by simpa [Layout.tag] using hp₁)
  · change roundMemory L values 2 _ _ = _
    rw [other 2 _ 2 (by decide) (by decide)]
    simpa +decide [Layout.tag, node, Nat.cast_mul] using roundMemory_arrXY L values 1
      (roundMemory L values 0 (paddingMemory L mem)) (by decide) hM (hinj 1) hi (by
        change roundMemory L values 0 (paddingMemory L mem) (L.packed + 4 * i + 2) = _
        rw [other 0 _ 2 (by decide) (by decide)]
        simpa [Layout.tag, Nat.cast_mul] using hp₂)
  · change roundMemory L values 2 _ _ = _
    apply roundMemory_arrZ L values _ hM (hinj 2) hi
    rw [other 1 _ 3 (by decide) (by decide), other 0 _ 3 (by decide) (by decide)]
    exact hp₃

/-- Every one of the `4N` native output cells equals the existing mathematical `Node.oneArray`.
This includes column-zero sentinels, empty and heavy buckets, and the entire padded tail. -/
theorem memory_oneArray (L : Layout) (values : Fin 3 → ℕ → ℤ) (mem : ℕ → ℕ)
    (hM : 0 < L.M) (hinj : ∀ j, Set.InjOn (values j) (↑(Finset.range (L.n j)) : Set ℕ))
    {u : ℕ} (hu : u < 4 * L.N) :
    memory L values mem (L.packed + u) = encode ((node L values).oneArray L.U u) := by
  obtain ⟨h₀, h₁, h₂, h₃⟩ := memory_cells L values mem hM hinj (i := u / 4) (by omega)
  have hgap : 3 * (((2 * L.U + 1 : ℕ) : ℤ)) + 1 = (L.gap : ℤ) := by
    dsimp only [Layout.gap]
    push_cast
    ring
  by_cases h1 : u % 4 = 1
  · rw [show L.packed + u = L.packed + 4 * (u / 4) + 1 by omega, h₁]
    simp only [Cslib.Algorithms.ThreeSum.ChanHe.Node.oneArray,
      Cslib.Algorithms.ThreeSum.oneArray, h1, ↓reduceIte, hgap, node]
  by_cases h2 : u % 4 = 2
  · rw [show L.packed + u = L.packed + 4 * (u / 4) + 2 by omega, h₂]
    simp only [Cslib.Algorithms.ThreeSum.ChanHe.Node.oneArray,
      Cslib.Algorithms.ThreeSum.oneArray, h2, ↓reduceIte, hgap, node, Nat.reduceEqDiff]
  by_cases h3 : u % 4 = 3
  · rw [show L.packed + u = L.packed + 4 * (u / 4) + 3 by omega, h₃]
    simp only [Cslib.Algorithms.ThreeSum.ChanHe.Node.oneArray,
      Cslib.Algorithms.ThreeSum.oneArray, h3, ↓reduceIte, hgap, node, Nat.reduceEqDiff]
  · rw [show L.packed + u = L.packed + 4 * (u / 4) by omega, h₀]
    simp only [Cslib.Algorithms.ThreeSum.ChanHe.Node.oneArray,
      Cslib.Algorithms.ThreeSum.oneArray, h1, h2, h3, ↓reduceIte, hgap]

/-- Every count cell and every used heavy cell survives subsequent rounds. -/
theorem memory_heavy (L : Layout) (values : Fin 3 → ℕ → ℤ) (mem : ℕ → ℕ)
    (hM : 0 < L.M) (hN : 2 * L.M ≤ L.N) (j : Fin 3) :
    memory L values mem (L.descriptor j) = (Place.heavyList (values j) (L.n j) L.M (L.n j)).length ∧
      ∀ k (hk : k < (Place.heavyList (values j) (L.n j) L.M (L.n j)).length),
        memory L values mem (L.heavy j + k) =
          encode ((Place.heavyList (values j) (L.n j) L.M (L.n j))[k]) := by
  have hround (j : Fin 3) (μ : ℕ → ℕ) :
      roundMemory L values j μ (L.descriptor j) =
          (Place.heavyList (values j) (L.n j) L.M (L.n j)).length ∧
        ∀ k (hk : k < (Place.heavyList (values j) (L.n j) L.M (L.n j)).length),
          roundMemory L values j μ (L.heavy j + k) =
            encode ((Place.heavyList (values j) (L.n j) L.M (L.n j))[k]) := by
    constructor
    · exact CountPlace.memory_descriptor ..
    · intro k hk
      exact CountPlace.memory_heavy _ _ _ _ _ _ _ _ _ _ _ _ _
        (L.heavy_end_le_packed j) (by dsimp only [Layout.heavy]; omega) hk
  have hnext := L.next_descriptor
  have hdesc01 : L.descriptor 0 < L.descriptor 1 := by
    dsimp only [Layout.heavy] at hnext
    omega
  have hdesc12 : L.descriptor 1 < L.descriptor 2 := by
    dsimp only [Layout.heavy] at hnext
    omega
  fin_cases j <;> simp only [Fin.mk_zero, Fin.mk_one]
  · obtain ⟨hc, hd⟩ := hround 0 (paddingMemory L mem)
    constructor
    · change roundMemory L values 2 _ _ = _
      rw [roundMemory_before L values 2 _ hM hN (by omega),
        roundMemory_before L values 1 _ hM hN (by omega)]
      exact hc
    · intro k hk
      have hlen := Place.length_heavyList_le (values 0) (L.n 0) L.M (L.n 0)
      change roundMemory L values 2 _ _ = _
      rw [roundMemory_before L values 2 _ hM hN (by omega),
        roundMemory_before L values 1 _ hM hN (by omega)]
      exact hd k hk
  · obtain ⟨hc, hd⟩ := hround 1 (roundMemory L values 0 (paddingMemory L mem))
    constructor
    · change roundMemory L values 2 _ _ = _
      rw [roundMemory_before L values 2 _ hM hN (by omega)]
      exact hc
    · intro k hk
      have hlen := Place.length_heavyList_le (values 1) (L.n 1) L.M (L.n 1)
      change roundMemory L values 2 _ _ = _
      rw [roundMemory_before L values 2 _ hM hN (by omega)]
      exact hd k hk
  · exact hround 2 (roundMemory L values 1 (roundMemory L values 0 (paddingMemory L mem)))

/-- Each complete round preserves all memory outside the concrete allocation. -/
theorem roundMemory_outside (L : Layout) (values : Fin 3 → ℕ → ℤ) (j : Fin 3)
    (mem : ℕ → ℕ) (hM : 0 < L.M) (hN : 2 * L.M ≤ L.N)
    {a : ℕ} (ha : a < L.base ∨ L.endpoint ≤ a) : roundMemory L values j mem a = mem a := by
  have ho := L.heavy_end_le_packed j
  have hb := L.base_le_descriptor j
  have hd := L.descriptor_lt_packed j
  have hn := L.n_le_total j
  have hp : L.packed + 4 * L.N ≤ L.endpoint := by
    dsimp only [Layout.endpoint, Layout.hist, Layout.scratch]
    omega
  have hk : L.scratch + L.n j ≤ L.hist := Nat.add_le_add_left hn _
  have hh : L.hist + L.M = L.endpoint := rfl
  have hs : L.scratch = L.packed + 4 * L.N := rfl
  have hout : L.heavy j = L.descriptor j + 1 := rfl
  apply CountPlace.memory_outside _ _ _ _ _ _ _ _ _ _ _ _ L.N _ hM hN
    (by omega) (by split_ifs <;> omega)
  all_goals rcases ha with ha | ha <;> omega

/-- Inputs, caller memory before the allocation, and memory beyond its endpoint are preserved. -/
theorem memory_outside (L : Layout) (values : Fin 3 → ℕ → ℤ) (mem : ℕ → ℕ)
    (hM : 0 < L.M) (hN : 2 * L.M ≤ L.N) {a : ℕ} (ha : a < L.base ∨ L.endpoint ≤ a) :
    memory L values mem a = mem a := by
  rw [memory, roundMemory_outside L values 2 _ hM hN ha,
    roundMemory_outside L values 1 _ hM hN ha, roundMemory_outside L values 0 _ hM hN ha]
  have hp : L.packed + 4 * L.N ≤ L.endpoint := by
    dsimp only [Layout.endpoint, Layout.hist, Layout.scratch]
    omega
  have hb : L.base ≤ L.packed := by dsimp only [Layout.packed]; omega
  have hnot : ¬(L.packed ≤ a ∧ a < L.packed + 4 * L.N) := by
    rcases ha with ha | ha <;> omega
  simp only [paddingMemory, Padding.memory, hnot, ↓reduceIte]

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.NodePacking
