/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORNativeGlobalTime
public import Complexity.Computability.WordRAM.InputArray
import Mathlib.Data.List.GetD
import all Complexity.Cryptanalysis.AddXNORNativeDissection
import all Complexity.Cryptanalysis.AddXNORNativeOrientedSearch
import all Complexity.Cryptanalysis.AddXNORNativeClassCounts

/-!
# Compact layout and derived physical width for native dissection

The original quarter arrays are contiguous, with the suffix reversed. Projection
and counter scratch buffers precede two reusable quarter arenas and a sparse
full-state dictionary. The dictionary base depends on quarter lists, not the
full-state address span. The logarithmic physical width also covers full-state
addresses and the potentially much larger multiplicity counter values.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.Native.Driver

open Cslib.WordRAM Quarter

/-- A single sufficient bound for every address, counter and immediate in the
native layout. It is an address/value capacity, not an occupied-cell bound. -/
def layoutLimit (m p a b c d : ℕ) : ℕ :=
  1000 * (1 + (a + b + c + d) + 2 ^ p + 2 ^ a + 2 ^ b + 2 ^ c + 2 ^ d +
    2 ^ m + 2 ^ (a + b) + 2 ^ (c + d))

/-- Physical words can address the dictionary and store every half-word count. -/
def globalWidth (m p a b c d : ℕ) : ℕ := (layoutLimit m p a b c d).log2 + 1

/-- The physical capacity follows from the chosen logarithmic width. -/
theorem layoutLimit_fits (m p a b c d : ℕ) :
    Fits (globalWidth m p a b c d) (layoutLimit m p a b c d) :=
  Nat.lt_log2_self

/-- A compact layout accommodating both orientations in the same memory. -/
def compactSearchLayout (m p a b c d : ℕ) :
    SearchLayout (globalWidth m p a b c d) m p a b c d :=
  let q := a + b + c + d
  let q₂ := 1 + 2 * q + 4 * 2 ^ p
  let q₃ := q₂ + b + c
  let h := q₃ + b + c
  let f := h + 2 ^ p
  let h₄ := f + 3 * (2 ^ a + 2 ^ d)
  let f₄ := h₄ + 2 ^ p
  let D := f₄ + 3 * (2 ^ a + 2 ^ d)
  { b₁ := 1
    b₂ := 1 + a
    b₃ := 1 + a + b + d
    b₄ := 1 + a + b
    q₂ := q₂
    q₃ := q₃
    h := h
    f := f
    h₄ := h₄
    f₄ := f₄
    D := D
    input₁ := by dsimp [q₂, q]; omega
    input₂ := by dsimp [q₂, q]; omega
    input₃ := by dsimp [q₂, q]; omega
    input₄ := by dsimp [q₂, q]; omega
    project₂ := by dsimp [q₃]; omega
    project₃ := by dsimp [h]; omega
    positive := by dsimp [f, h, q₃, q₂]; omega
    heads := le_rfl
    arena := le_rfl
    heads₄ := le_rfl
    boundary := le_rfl
    capacity := (layoutLimit_fits m p a b c d).of_le (by
      dsimp [D, f₄, h₄, f, h, q₃, q₂, q, layoutLimit]
      have hp := Nat.two_pow_pos p
      have ha := Nat.two_pow_pos a
      have hb := Nat.two_pow_pos b
      have hc := Nat.two_pow_pos c
      have hd := Nat.two_pow_pos d
      have hm := Nat.two_pow_pos m
      have hab := Nat.two_pow_pos (a + b)
      have hcd := Nat.two_pow_pos (c + d)
      omega) }

/-- The two counter pairs occupy disjoint reusable buffers before the class arenas. -/
def compactCounterLayout (m p a b c d : ℕ) : CounterLayout (compactSearchLayout m p a b c d) :=
  let q := 1 + (a + b + c + d)
  let B := q + (a + b)
  let r := B + 2 * 2 ^ p
  let C := r + (c + d)
  { prefixBase := 1
    suffixBase := 1 + a + b
    q := q
    B := B
    r := r
    C := C
    prefixEnd := by dsimp [q]; omega
    suffixEnd := by dsimp [q]; omega
    firstEnd := by dsimp [q, compactSearchLayout]; omega
    secondEnd := by dsimp [q, compactSearchLayout]; omega
    thirdEnd := by dsimp [q, compactSearchLayout]; omega
    fourthEnd := by dsimp [q, compactSearchLayout]; omega
    projection := le_rfl
    separation := le_rfl
    projectionBack := le_rfl
    below := by dsimp [C, r, B, q, compactSearchLayout]; omega
    capacityForward := (layoutLimit_fits m p a b c d).of_le (by
      dsimp [B, q, layoutLimit]
      have hp := Nat.two_pow_pos p
      have ha := Nat.two_pow_pos a
      have hb := Nat.two_pow_pos b
      have hc := Nat.two_pow_pos c
      have hd := Nat.two_pow_pos d
      have hm := Nat.two_pow_pos m
      have hab := Nat.two_pow_pos (a + b)
      have hcd := Nat.two_pow_pos (c + d)
      omega)
    capacityBackward := (layoutLimit_fits m p a b c d).of_le (by
      dsimp [C, r, B, q, layoutLimit]
      have hp := Nat.two_pow_pos p
      have ha := Nat.two_pow_pos a
      have hb := Nat.two_pow_pos b
      have hc := Nat.two_pow_pos c
      have hd := Nat.two_pow_pos d
      have hm := Nat.two_pow_pos m
      have hab := Nat.two_pow_pos (a + b)
      have hcd := Nat.two_pow_pos (c + d)
      omega)
    capacityScan := (layoutLimit_fits m p a b c d).of_le (by
      dsimp [C, r, B, q, layoutLimit]
      have hp := Nat.two_pow_pos p
      have ha := Nat.two_pow_pos a
      have hb := Nat.two_pow_pos b
      have hc := Nat.two_pow_pos c
      have hd := Nat.two_pow_pos d
      have hm := Nat.two_pow_pos m
      have hab := Nat.two_pow_pos (a + b)
      have hcd := Nat.two_pow_pos (c + d)
      omega) }

/-- The initial workspace support depends on quarter enumerations, not all states. -/
theorem compactSearchLayout_dictionary (m p a b c d : ℕ) :
    (compactSearchLayout m p a b c d).D =
      1 + 2 * (a + b + c + d) + 2 * (b + c) + 6 * 2 ^ p + 6 * (2 ^ a + 2 ^ d) := by
  dsimp [compactSearchLayout]
  omega

/-- Full-state dictionary slots, release pointers and actual counter loads all fit. -/
theorem compactSearchLayout_fits (m p a b c d : ℕ) :
    let L := compactSearchLayout m p a b c d
    Fits (globalWidth m p a b c d) (L.D + 4 * 2 ^ m + 8) ∧
      Fits (globalWidth m p a b c d) (2 * L.q₂ + 2 * 2 ^ p + 4) := by
  have hp := Nat.two_pow_pos p
  have ha := Nat.two_pow_pos a
  have hb := Nat.two_pow_pos b
  have hc := Nat.two_pow_pos c
  have hd := Nat.two_pow_pos d
  have hm := Nat.two_pow_pos m
  have hab := Nat.two_pow_pos (a + b)
  have hcd := Nat.two_pow_pos (c + d)
  constructor <;> apply (layoutLimit_fits m p a b c d).of_le <;>
    dsimp [compactSearchLayout, layoutLimit] <;> omega

end Cslib.Cryptanalysis.AddXNOR.Native.Driver

namespace Cslib.Cryptanalysis.AddXNOR.Native.Driver

/-- Original operands in the physical order consumed by both native directions.
The standard RAM input convention supplies its ordinary length header. Seeds,
widths and quarter lengths remain immediate parameters of the fixed graph. -/
def quarterInput {m : ℕ} (as bs cs ds : List (BitVec m)) : List ℕ :=
  (as ++ (bs ++ (ds.reverse ++ cs.reverse))).map BitVec.toNat

private theorem input_block {m : ℕ} (pre payload post : List (BitVec m))
    (i : ℕ) (hi : i < payload.length) :
    (Cslib.WordRAM.Data.init ((pre ++ (payload ++ post)).map BitVec.toNat) :
      Cslib.WordRAM.Data 40).mem (pre.length + 1 + i) = payload[i].toNat := by
  have h := Cslib.WordRAM.Data.init_realizes_append (r := 40)
    (pre.map BitVec.toNat) (payload.map BitVec.toNat) (post.map BitVec.toNat)
    ⟨i, by simpa only [List.length_map] using hi⟩
  simpa only [Cslib.WordRAM.Block.read, List.length_map, List.get_eq_getElem, List.getElem_map,
    List.map_append] using h

open Cslib.WordRAM Quarter

/-- Every original quarter, contiguous half and initially zero dictionary cell
comes from the actual initialized input, for arbitrary quarter lengths and widths. -/
theorem quarterInput_raw {m p : ℕ} (as bs cs ds : List (BitVec m)) :
    let L := compactSearchLayout m p as.length bs.length cs.length ds.length
    let K := compactCounterLayout m p as.length bs.length cs.length ds.length
    let x : Data 40 := Data.init (quarterInput as bs cs ds)
    L.Raw as bs cs ds (x.comap bank) ∧
      (∀ i (hi : i < (as ++ bs).length), x.mem (K.prefixBase + i) = (as ++ bs)[i].toNat) ∧
      (∀ i (hi : i < (cs ++ ds).reverse.length),
        x.mem (K.suffixBase + i) = (cs ++ ds).reverse[i].toNat) := by
  dsimp only
  have block := input_block (m := m)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i hi
    simpa only [compactSearchLayout, Data.comap_mem, quarterInput, List.nil_append,
      List.length_nil, Nat.zero_add] using block [] as (bs ++ (ds.reverse ++ cs.reverse)) i hi
  · intro i hi
    simpa only [compactSearchLayout, Data.comap_mem, quarterInput, Nat.add_comm as.length 1]
      using block as bs (ds.reverse ++ cs.reverse) i hi
  · intro i hi
    simpa only [compactSearchLayout, Data.comap_mem, quarterInput, List.length_append,
      List.length_reverse, List.append_nil, List.append_assoc, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using block (as ++ (bs ++ ds.reverse)) cs.reverse [] i hi
  · intro i hi
    simpa only [compactSearchLayout, Data.comap_mem, quarterInput, List.length_append,
      List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using block (as ++ bs) ds.reverse cs.reverse i hi
  · intro a ha
    have hlen : (quarterInput as bs cs ds).length < a := by
      simp only [quarterInput, List.length_map, List.length_append, List.length_reverse]
      rw [compactSearchLayout_dictionary] at ha
      omega
    have apos : a ≠ 0 := by omega
    simp only [Data.comap_mem, Data.init, apos, ↓reduceIte]
    exact List.getD_eq_default _ _ (by omega)
  · intro i hi
    simpa only [compactCounterLayout, quarterInput, List.length_nil, Nat.zero_add,
      List.nil_append, List.append_assoc] using block [] (as ++ bs) (ds.reverse ++ cs.reverse) i hi
  · intro i hi
    simpa only [compactCounterLayout, quarterInput, List.length_append, List.reverse_append,
      List.append_assoc, List.append_nil, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using block (as ++ bs) (ds.reverse ++ cs.reverse) [] i (by
        simpa only [List.length_append, List.length_reverse, Nat.add_comm] using hi)

/-- The initialized input, including its length word, fits the derived physical width. -/
theorem quarterInput_fits {m p : ℕ} (as bs cs ds : List (BitVec m)) :
    InputFits (globalWidth m p as.length bs.length cs.length ds.length)
      (quarterInput as bs cs ds) := by
  have cap := layoutLimit_fits m p as.length bs.length cs.length ds.length
  have hm := Nat.two_pow_pos m
  have hp := Nat.two_pow_pos p
  have hA := Nat.two_pow_pos as.length
  have hB := Nat.two_pow_pos bs.length
  have hC := Nat.two_pow_pos cs.length
  have hD := Nat.two_pow_pos ds.length
  have hab := Nat.two_pow_pos (as.length + bs.length)
  have hcd := Nat.two_pow_pos (cs.length + ds.length)
  constructor
  · apply cap.of_le
    simp only [quarterInput, List.length_map, List.length_append, List.length_reverse]
    dsimp only [layoutLimit]
    omega
  · intro v hv
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hv
    exact cap.of_le (by
      have ha := a.isLt
      dsimp only [layoutLimit]
      omega)

end Cslib.Cryptanalysis.AddXNOR.Native.Driver
