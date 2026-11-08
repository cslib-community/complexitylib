/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORNativeOrientation
import all Complexity.Cryptanalysis.AddXNORNativeClassSearch
import all Complexity.Cryptanalysis.AddXNORNativeClassSemantics
import all Complexity.Cryptanalysis.AddXNORNativeDictionary

/-!
# Two native class-search orientations with dictionary release

Both directions execute the proved native construction. Inverse retention uses
complement conjugacy of the reversed chain. Returned operator words are decoded
in the selected orientation; no inverse state is interpreted as an original
forward state. Each class releases its actual dictionary chain, restores witness
registers, frames original input and leaves the dictionary region zero for reuse.
These are class-lifetime components of [WangLvShenZhang2027], Theorem 7, PDF p. 22.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.Native.Quarter

open Cslib.WordRAM

/-- Raw physical layout shared by both orientations. The projection and quarter
arenas admit either ordering; no semantic execution facts are fields. -/
structure SearchLayout (W m p a b c d : ℕ) where
  /-- Original operand bases. -/
  b₁ : ℕ
  /-- Forward original second-quarter base. -/
  b₂ : ℕ
  /-- Reversed original third-quarter base. -/
  b₃ : ℕ
  /-- Reversed original fourth-quarter base. -/
  b₄ : ℕ
  /-- Two projected middle-quarter buffers. -/
  q₂ : ℕ
  /-- Second projection scratch base. -/
  q₃ : ℕ
  /-- Quarter heads, record arenas and dictionary base. -/
  h : ℕ
  /-- First quarter-record arena base. -/
  f : ℕ
  /-- Second quarter-head array base. -/
  h₄ : ℕ
  /-- Second quarter-record arena base. -/
  f₄ : ℕ
  /-- Sparse full-state dictionary base. -/
  D : ℕ
  input₁ : b₁ + a ≤ q₂
  input₂ : b₂ + b ≤ q₂
  input₃ : b₃ + c ≤ q₂
  input₄ : b₄ + d ≤ q₂
  project₂ : q₂ + b + c ≤ q₃
  project₃ : q₃ + b + c ≤ h
  positive : 0 < f
  heads : h + 2 ^ p ≤ f
  arena : f + 3 * (2 ^ a + 2 ^ d) ≤ h₄
  heads₄ : h₄ + 2 ^ p ≤ f₄
  boundary : f₄ + 3 * (2 ^ a + 2 ^ d) ≤ D
  capacity : Fits W (4 * (b₁ + b₂ + b₃ + b₄ + q₂ + q₃ + h + f + h₄ + f₄ + D +
    a + b + c + d) + 20 * 2 ^ m + 10 * 2 ^ p +
    10 * 2 ^ a + 10 * 2 ^ b + 10 * 2 ^ c + 10 * 2 ^ d + 64)

/-- The sole memory premises: original arrays and an initially empty table. -/
def SearchLayout.Raw {W m p : ℕ} (as bs cs ds : List (BitVec m))
    (L : SearchLayout W m p as.length bs.length cs.length ds.length) (x : Data 32) : Prop :=
  (∀ i (hi : i < as.length), x.mem (L.b₁ + i) = as[i].toNat) ∧
  (∀ i (hi : i < bs.length), x.mem (L.b₂ + i) = bs[i].toNat) ∧
  (∀ i (hi : i < cs.reverse.length), x.mem (L.b₃ + i) = cs.reverse[i].toNat) ∧
  (∀ i (hi : i < ds.reverse.length), x.mem (L.b₄ + i) = ds.reverse[i].toNat) ∧
  (∀ a, L.D ≤ a → x.mem a = 0)

/-- Exact previously proved class-search budget, including all setup. -/
def searchTime {m p : ℕ} (as bs cs ds : List (BitVec m)) (s t : BitVec m) (g : BitVec p) : ℕ :=
  let fs := fun k : BitVec p => Forward.records as s p k.toNat
  let rs := inverseRecords ds t p
  ((10 * bs.length + 8) + (10 * cs.length + 8)) +
    ((7 + (4 * 2 ^ p + 2 ^ as.length * (11 * as.length + 22) + 10) +
      (7 + (4 * 2 ^ p + 2 ^ ds.length * (18 * ds.length + 37) + 10))) +
      (8 + ((5 + classRetainTime bs g fs 0 (2 ^ bs.length)) +
        (8 + (2 + (4 + classProbeTime cs g rs 0 (2 ^ cs.length)))))))

/-- The actual oriented native kernel. Reversal changes operand order and state
convention together. Original arrays already have the required physical orders. -/
@[expose] def orientedKernel {W m p a b c d : ℕ} (L : SearchLayout W m p a b c d)
    (s t g : ℕ) (back : Bool) : Code .standard 32 :=
  if back then searchClass L.b₄ d L.b₃ c L.b₂ b L.b₁ a L.q₂ L.q₃
    (2 ^ m) (2 ^ p) s t g L.h L.f L.h₄ L.f₄ L.D
  else searchClass L.b₁ a L.b₂ b L.b₃ c L.b₄ d L.q₂ L.q₃
    (2 ^ m) (2 ^ p) s t g L.h L.f L.h₄ L.f₄ L.D

/-- Interpretation of the four returned packed words in the original order. -/
def orientedWitness {m : ℕ} (back : Bool) (as bs cs ds : List (BitVec m)) (y : Data 32) :
    List (Bool × BitVec m) :=
  if back then
    ((decode as.length (y.regs firstOperators)).reverse.zip as) ++
      ((decode bs.length (y.regs operators)).reverse.zip bs) ++
      ((decode cs.length (y.regs bits)).reverse.zip cs) ++
      ((decode ds.length (y.regs operand - 1)).reverse.zip ds)
  else ((decode as.length (y.regs operand - 1)).zip as) ++
      ((decode bs.length (y.regs bits)).zip bs) ++
      ((decode cs.length (y.regs operators)).zip cs) ++
      ((decode ds.length (y.regs firstOperators)).zip ds)

/-- Reversing every decoded quarter together with its operands gives an original
witness, even for non-self-inverse additions and unequal quarter lengths. -/
theorem inverse_witness_sound {m : ℕ} (as bs cs ds : List (BitVec m))
    (s t : BitVec m) (y : Data 32)
    (he : eval (((decode ds.reverse.length (y.regs operand - 1)).zip ds.reverse) ++
      ((decode cs.reverse.length (y.regs bits)).zip cs.reverse) ++
      ((decode bs.reverse.length (y.regs operators)).zip bs.reverse) ++
      ((decode as.reverse.length (y.regs firstOperators)).zip as.reverse)) (~~~t) = ~~~s) :
    eval (orientedWitness true as bs cs ds y) s = t := by
  have hh := (eval_reverse_not _ (~~~t) (~~~s)).mpr he
  simp only [BitVec.not_not, List.reverse_append, List.length_reverse,
    List.zip_eq_zipWith] at hh
  rw [List.reverse_zipWith (by simp only [decode_length, List.length_reverse]),
    List.reverse_zipWith (by simp only [decode_length, List.length_reverse]),
    List.reverse_zipWith (by simp only [decode_length, List.length_reverse]),
    List.reverse_zipWith (by simp only [decode_length, List.length_reverse])] at hh
  simpa only [orientedWitness, List.reverse_reverse, Bool.true_eq, ↓reduceIte,
    List.zip_eq_zipWith, List.append_assoc] using hh

/-- Reverse the raw layout without moving or reinterpreting any memory cell. -/
@[expose] def reverseLayout {W m p : ℕ} (as bs cs ds : List (BitVec m))
    (L : SearchLayout W m p as.length bs.length cs.length ds.length) :
    SearchLayout W m p ds.reverse.length cs.reverse.length bs.reverse.length as.reverse.length where
  b₁ := L.b₄
  b₂ := L.b₃
  b₃ := L.b₂
  b₄ := L.b₁
  q₂ := L.q₂
  q₃ := L.q₃
  h := L.h
  f := L.f
  h₄ := L.h₄
  f₄ := L.f₄
  D := L.D
  input₁ := by simpa only [List.length_reverse] using L.input₄
  input₂ := by simpa only [List.length_reverse] using L.input₃
  input₃ := by simpa only [List.length_reverse] using L.input₂
  input₄ := by simpa only [List.length_reverse] using L.input₁
  project₂ := by have := L.project₂; simp only [List.length_reverse]; omega
  project₃ := by have := L.project₃; simp only [List.length_reverse]; omega
  positive := L.positive
  heads := L.heads
  arena := by have := L.arena; simp only [List.length_reverse]; omega
  heads₄ := L.heads₄
  boundary := by have := L.boundary; simp only [List.length_reverse]; omega
  capacity := L.capacity.of_le (by simp only [List.length_reverse]; omega)

/-- Raw input is available in the conjugated orientation in the very same memory. -/
theorem SearchLayout.Raw.reverse {W m p : ℕ} (as bs cs ds : List (BitVec m))
    (L : SearchLayout W m p as.length bs.length cs.length ds.length) (x : Data 32)
    (hx : L.Raw as bs cs ds x) :
    (reverseLayout as bs cs ds L).Raw ds.reverse cs.reverse bs.reverse as.reverse x := by
  exact ⟨hx.2.2.2.1, hx.2.2.1,
    by simpa only [reverseLayout, List.reverse_reverse] using hx.2.1,
    by simpa only [reverseLayout, List.reverse_reverse] using hx.1, hx.2.2.2.2⟩

/-- Retained insertion count, including duplicate indexed states. -/
def insertionCount {m p : ℕ} (as bs : List (BitVec m)) (s : BitVec m) (g : BitVec p) : ℕ :=
  (classEntries bs g (fun k => Forward.records as s p k.toNat) 0 (2 ^ bs.length)).length

/-- Ordinary kernel with the raw-layout record. The dictionary contents, key
bounds and erase/frame contracts are all derived by native construction. -/
theorem forward_kernel_exec {W m p : ℕ} (hp : p ≤ m)
    (as bs cs ds : List (BitVec m)) (s t : BitVec m) (g : BitVec p)
    (L : SearchLayout W m p as.length bs.length cs.length ds.length) (x : Data 32)
    (hx : L.Raw as bs cs ds x) :
    ∃ y, ExecWithin W (orientedKernel L s.toNat t.toNat g.toNat false) x y
        (searchTime as bs cs ds s t g) ∧
      StoresWithin W (orientedKernel L s.toNat t.toNat g.toNat false) x y
        (searchTime as bs cs ds s t g) (searchStores as bs cs ds s g) ∧
      (y.regs operand ≠ 0 ↔ PackedClassSolution as bs cs ds s t g) ∧
      (y.regs operand ≠ 0 → eval (orientedWitness false as bs cs ds y) s = t) ∧
      ∃ keys, Dictionary.Valid y.mem L.D (y.regs Dictionary.top) keys ∧
        keys.length ≤ insertionCount as bs s g ∧
        (∀ a, a < L.q₂ → y.mem a = x.mem a) ∧
        (∀ a, L.D ≤ a → Dictionary.erasedMemory y.mem L.D keys a = 0) ∧
        (∀ k ∈ keys, k < 2 ^ m) ∧ y.regs Dictionary.table = L.D := by
  obtain ⟨y, he, stored, hh, _, hw, _, keys, hk, hl, frame, erased, bound, table⟩ :=
    searchClass_exec hp as bs cs ds s t g x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1
      L.input₁ L.input₂ L.input₃ L.input₄
      (by have := L.project₂; omega) (by have := L.project₃; omega)
      L.positive L.heads (by have := L.arena; have := Nat.zero_le (2 ^ ds.length); omega) L.heads₄
      (by have := L.boundary; have := Nat.zero_le (2 ^ as.length); omega) hx.2.2.2.2 L.capacity
  exact ⟨y, he, stored, hh, hw, keys, hk, hl, frame, erased, bound, table⟩

/-- Either actual native orientation decides the original class and returns an
original-chain witness. No correctness of inverse-retained payloads is assumed. -/
theorem oriented_kernel_exec {W m p : ℕ} (hp : p ≤ m)
    (as bs cs ds : List (BitVec m)) (s t : BitVec m) (g : BitVec p)
    (L : SearchLayout W m p as.length bs.length cs.length ds.length) (back : Bool)
    (x : Data 32) (hx : L.Raw as bs cs ds x) :
    ∃ y, ExecWithin W
        (orientedKernel L (if back then (~~~t).toNat else s.toNat)
          (if back then (~~~s).toNat else t.toNat)
          (if back then (~~~g).toNat else g.toNat) back)
        x y (if back then
          searchTime ds.reverse cs.reverse bs.reverse as.reverse (~~~t) (~~~s) (~~~g)
          else searchTime as bs cs ds s t g) ∧
      StoresWithin W
        (orientedKernel L (if back then (~~~t).toNat else s.toNat)
          (if back then (~~~s).toNat else t.toNat)
          (if back then (~~~g).toNat else g.toNat) back)
        x y (if back then
          searchTime ds.reverse cs.reverse bs.reverse as.reverse (~~~t) (~~~s) (~~~g)
          else searchTime as bs cs ds s t g)
        (if back then searchStores ds.reverse cs.reverse bs.reverse as.reverse (~~~t) (~~~g)
          else searchStores as bs cs ds s g) ∧
      (y.regs operand ≠ 0 ↔ PackedClassSolution as bs cs ds s t g) ∧
      (y.regs operand ≠ 0 → eval (orientedWitness back as bs cs ds y) s = t) ∧
      ∃ keys, Dictionary.Valid y.mem L.D (y.regs Dictionary.top) keys ∧
        keys.length ≤ (if back then insertionCount ds.reverse cs.reverse (~~~t) (~~~g)
          else insertionCount as bs s g) ∧
        (∀ a, a < L.q₂ → y.mem a = x.mem a) ∧
        (∀ a, L.D ≤ a → Dictionary.erasedMemory y.mem L.D keys a = 0) ∧
        (∀ k ∈ keys, k < 2 ^ m) ∧ y.regs Dictionary.table = L.D := by
  cases back
  · exact forward_kernel_exec hp as bs cs ds s t g L x hx
  · obtain ⟨y, he, stored, hh, hw, keys, hk, hl, frame, erased, bound, table⟩ :=
      forward_kernel_exec hp ds.reverse cs.reverse bs.reverse as.reverse (~~~t) (~~~s) (~~~g)
        (reverseLayout as bs cs ds L) x (SearchLayout.Raw.reverse as bs cs ds L x hx)
    refine ⟨y, ?_, ?_, ?_, ?_, keys, hk, hl, frame, erased, bound, table⟩
    · simpa only [orientedKernel, Bool.true_eq, Bool.false_eq_true, ↓reduceIte, reverseLayout,
        List.length_reverse] using he
    · simpa only [orientedKernel, Bool.true_eq, Bool.false_eq_true, ↓reduceIte, reverseLayout,
        List.length_reverse] using stored
    · exact hh.trans (packedClassSolution_reverse_iff hp as bs cs ds s t g)
    · intro hit
      exact inverse_witness_sound as bs cs ds s t y (hw hit)

/-- Save the one witness register that dictionary release uses as scratch. -/
@[expose] def releaseWitness : Code .standard 32 :=
  .seq (ram[ queryOperators ← bits ]) (.seq Dictionary.release (ram[ bits ← queryOperators ]))

/-- Release reads the physical chain and restores every reported witness word. -/
theorem releaseWitness_exec {W D : ℕ} (keys : List ℕ) (x : Data 32)
    (hD : x.regs Dictionary.table = D)
    (hk : Dictionary.Valid x.mem D (x.regs Dictionary.top) keys) (h3 : Fits W 3)
    (hfit : ∀ k ∈ keys, Fits W (D + 3 * k + 4)) :
    ∃ y, ExecWithin W releaseWitness x y (12 * keys.length + 7) ∧
      y.mem = Dictionary.erasedMemory x.mem D keys ∧
      y.regs operand = x.regs operand ∧ y.regs bits = x.regs bits ∧
      y.regs operators = x.regs operators ∧ y.regs firstOperators = x.regs firstOperators := by
  let z := x.set queryOperators (x.regs bits)
  have hz : ExecWithin (B := .standard) W (ram[ queryOperators ← bits ]) x z 1 := .copy
  obtain ⟨u, hu, um, _⟩ := Dictionary.release_exec keys z
    ((hz.regs_eq (by decide)).trans hD) rfl hk.chain hk.nodup h3 hfit
  let y := u.set bits (u.regs queryOperators)
  have hy : ExecWithin (B := .standard) W (ram[ bits ← queryOperators ]) u y 1 := .copy
  have hq := hu.regs_eq (by decide : Dictionary.release.Preserves queryOperators)
  refine ⟨y, (hz.seq (hu.seq hy)).mono (by omega), um, ?_, ?_, ?_, ?_⟩
  · exact ((hz.seq (hu.seq hy)).regs_eq (by decide : releaseWitness.Preserves operand))
  · simpa only [y, Data.set_regs, Function.update_self, z, Data.set_regs,
      Function.update_self] using hq
  · exact ((hz.seq (hu.seq hy)).regs_eq (by decide : releaseWitness.Preserves operators))
  · exact ((hz.seq (hu.seq hy)).regs_eq (by decide : releaseWitness.Preserves firstOperators))

/-- Instruction budget including release of every retained indexed record, a
conservative bound when collisions shorten the actual physical release chain. -/
def orientedTime {m p : ℕ} (back : Bool) (as bs cs ds : List (BitVec m))
    (s t : BitVec m) (g : BitVec p) : ℕ :=
  (if back then searchTime ds.reverse cs.reverse bs.reverse as.reverse (~~~t) (~~~s) (~~~g)
    else searchTime as bs cs ds s t g) +
  12 * (if back then insertionCount ds.reverse cs.reverse (~~~t) (~~~g)
    else insertionCount as bs s g) + 7

/-- Stores per dictionary lifetime, without charging the write-free stream. -/
def orientedStores {m p : ℕ} (back : Bool) (as bs cs ds : List (BitVec m))
    (s t : BitVec m) (g : BitVec p) : ℕ :=
  (if back then searchStores ds.reverse cs.reverse bs.reverse as.reverse (~~~t) (~~~g)
    else searchStores as bs cs ds s g) +
  12 * (if back then insertionCount ds.reverse cs.reverse (~~~t) (~~~g)
    else insertionCount as bs s g) + 7

/-- An oriented native lifetime, including release even on a successful hit. -/
@[expose] def orientedCycle {W m p a b c d : ℕ} (L : SearchLayout W m p a b c d)
    (s t g : ℕ) (back : Bool) : Code .standard 32 :=
  .seq (orientedKernel L s t g back) releaseWitness

/-- Both orientations leave reusable empty dictionary memory, preserve original
arrays and return an original witness. All release invariants come from stores. -/
theorem oriented_cycle_exec {W m p : ℕ} (hp : p ≤ m)
    (as bs cs ds : List (BitVec m)) (s t : BitVec m) (g : BitVec p)
    (L : SearchLayout W m p as.length bs.length cs.length ds.length) (back : Bool)
    (x : Data 32) (hx : L.Raw as bs cs ds x)
    (hfit : Fits W (L.D + 4 * 2 ^ m + 8)) :
    ∃ y, ExecWithin W
        (orientedCycle L (if back then (~~~t).toNat else s.toNat)
          (if back then (~~~s).toNat else t.toNat)
          (if back then (~~~g).toNat else g.toNat) back)
        x y (orientedTime back as bs cs ds s t g) ∧
      StoresWithin W
        (orientedCycle L (if back then (~~~t).toNat else s.toNat)
          (if back then (~~~s).toNat else t.toNat)
          (if back then (~~~g).toNat else g.toNat) back)
        x y (orientedTime back as bs cs ds s t g) (orientedStores back as bs cs ds s t g) ∧
      (y.regs operand ≠ 0 ↔ PackedClassSolution as bs cs ds s t g) ∧
      (y.regs operand ≠ 0 → eval (orientedWitness back as bs cs ds y) s = t) ∧
      (∀ a, a < L.q₂ → y.mem a = x.mem a) ∧ L.Raw as bs cs ds y := by
  obtain ⟨u, hu, stored, hh, hw, keys, hk, hl, frame, erased, bound, table⟩ :=
    oriented_kernel_exec hp as bs cs ds s t g L back x hx
  obtain ⟨y, hy, ym, yo, yb, yops, yf⟩ := releaseWitness_exec keys u table hk
    (hfit.of_le (by omega))
    (by intro k hk; have := bound k hk; exact hfit.of_le (by omega))
  have qD : L.q₂ ≤ L.D := calc
    L.q₂ ≤ L.q₂ + bs.length + cs.length := by omega
    _ ≤ L.q₃ := L.project₂
    _ ≤ L.q₃ + bs.length + cs.length := by omega
    _ ≤ L.h := L.project₃
    _ ≤ L.h + 2 ^ p := Nat.le_add_right _ _
    _ ≤ L.f := L.heads
    _ ≤ L.f + 3 * (2 ^ as.length + 2 ^ ds.length) := Nat.le_add_right _ _
    _ ≤ L.h₄ := L.arena
    _ ≤ L.h₄ + 2 ^ p := Nat.le_add_right _ _
    _ ≤ L.f₄ := L.heads₄
    _ ≤ L.f₄ + 3 * (2 ^ as.length + 2 ^ ds.length) := Nat.le_add_right _ _
    _ ≤ L.D := L.boundary
  have original (a : ℕ) (ha : a < L.q₂) : y.mem a = x.mem a := by
    rw [ym, Dictionary.erasedMemory_below _ _ _ _ (ha.trans_le qD), frame a ha]
  refine ⟨y, (hu.seq hy).mono (by dsimp only [orientedTime]; omega),
    (stored.seq hy.stores).mono (by dsimp only [orientedTime]; omega)
      (by dsimp only [orientedStores]; omega), ?_, ?_, original, ?_⟩
  · rwa [yo]
  · intro hit
    have witness : orientedWitness back as bs cs ds y = orientedWitness back as bs cs ds u := by
      simp only [orientedWitness, yo, yb, yops, yf]
    rw [witness]
    exact hw (yo ▸ hit)
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i hi; rw [original _ (by have := L.input₁; omega)]; exact hx.1 i hi
    · intro i hi; rw [original _ (by have := L.input₂; omega)]; exact hx.2.1 i hi
    · intro i hi
      rw [original _ (by have := L.input₃; simp only [List.length_reverse] at hi; omega)]
      exact hx.2.2.1 i hi
    · intro i hi
      rw [original _ (by have := L.input₄; simp only [List.length_reverse] at hi; omega)]
      exact hx.2.2.2.1 i hi
    · intro a ha; rw [ym]; exact erased a ha

end Cslib.Cryptanalysis.AddXNOR.Native.Quarter
