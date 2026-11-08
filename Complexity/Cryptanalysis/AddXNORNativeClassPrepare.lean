/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORNativeClassSemantics
public import Complexity.Cryptanalysis.AddXNORNativeDualPreparation
import all Complexity.Cryptanalysis.AddXNORNativeClassSemantics
import all Complexity.Cryptanalysis.AddXNORNativeBuckets
import all Complexity.Cryptanalysis.AddXNORNativeBackward

/-!
# Native preparation of both quarter bucket families

Prepare forward first-quarter and inverse fourth-quarter records in disjoint
arenas before storing the retained class. Both bucket families and input/dictionary
frames are conclusions of execution, not caller-supplied traversal invariants.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.Native.Quarter

open Cslib.WordRAM

/-- Both native quarter constructions with all register transfers charged. -/
@[expose] def prepareClassBuckets (b n b₄ n₄ M s t h f h₄ f₄ N : ℕ) : Code .standard 32 :=
  .seq (inverseSetup b n M s h f N)
    (.seq prepare (.seq (inverseSetup b₄ n₄ M t h₄ f₄ N) Backward.prepare))

/-- Exact actual memory after both preparations. -/
def pairMemory {m : ℕ} (as ds : List (BitVec m)) (s t : BitVec m) (mem : ℕ → ℕ)
    (h f h₄ f₄ p : ℕ) : ℕ → ℕ :=
  Backward.preparedMemory ds t
    (clear (preparedMemory as s (clear mem h (2 ^ p)) h f (2 ^ p) (2 ^ as.length))
      h₄ (2 ^ p)) h₄ f₄ (2 ^ p) (2 ^ ds.length)

private theorem transfer_exec {W : ℕ} (b n M s h f N : ℕ) (x : Data 32)
    (hfit : Fits W (b + n + M + s + h + f + N)) :
    ExecWithin W (inverseSetup b n M s h f N) x
      (x.set base b |>.set count n |>.set modulus M |>.set initial s
        |>.set heads h |>.set frontier f |>.set keyModulus N) 7 := by
  have hb : Fits W b := hfit.of_le (by omega)
  have hn : Fits W n := hfit.of_le (by omega)
  have hm : Fits W M := hfit.of_le (by omega)
  have hs : Fits W s := hfit.of_le (by omega)
  have hh : Fits W h := hfit.of_le (by omega)
  have hf : Fits W f := hfit.of_le (by omega)
  have hN : Fits W N := hfit.of_le (by omega)
  ram_eval [inverseSetup, hb, hn, hm, hs, hh, hf, hN,
    base, count, modulus, initial, heads, frontier, keyModulus, Fin.mk.injEq]

/-- Raw original operands produce both complete indexed linked-bucket families.
All memory before the first heads and after both arenas is unchanged. -/
theorem prepareClassBuckets_exec {W m p b b₄ h f h₄ f₄ D : ℕ}
    (as ds : List (BitVec m)) (s t : BitVec m) (x : Data 32)
    (hfirst : ∀ i (hi : i < as.length), x.mem (b + i) = as[i].toNat)
    (hfourth : ∀ i (hi : i < ds.reverse.length), x.mem (b₄ + i) = ds.reverse[i].toNat)
    (hend₁ : b + as.length ≤ h) (hend₄ : b₄ + ds.length ≤ h)
    (hfpos : 0 < f) (hheads : h + 2 ^ p ≤ f)
    (harenas : f + 3 * 2 ^ as.length ≤ h₄) (hheads₄ : h₄ + 2 ^ p ≤ f₄)
    (hboundary : f₄ + 3 * 2 ^ ds.length ≤ D)
    (hfit : Fits W (b + as.length + b₄ + ds.length + h + f + h₄ + f₄ + D +
      4 * 2 ^ p + 4 * 2 ^ m + 5 * 2 ^ as.length + 5 * 2 ^ ds.length + 16)) :
    ∃ y, ExecWithin W
        (prepareClassBuckets b as.length b₄ ds.length (2 ^ m) s.toNat t.toNat
          h f h₄ f₄ (2 ^ p)) x y
        (7 + (4 * 2 ^ p + 2 ^ as.length * (11 * as.length + 22) + 10) +
          (7 + (4 * 2 ^ p + 2 ^ ds.length * (18 * ds.length + 37) + 10))) ∧
      y.mem = pairMemory as ds s t x.mem h f h₄ f₄ p ∧
      (∀ k : BitVec p, Linked y.mem (f + 3 * 2 ^ as.length) (y.mem (h + k.toNat))
        (Forward.records as s p k.toNat)) ∧
      (∀ k : BitVec p, Linked y.mem (f₄ + 3 * 2 ^ ds.length) (y.mem (h₄ + k.toNat))
        (inverseRecords ds t p k)) ∧
      (∀ a, a < h ∨ D ≤ a → y.mem a = x.mem a) := by
  have hP := Nat.two_pow_pos p
  have hA := Nat.two_pow_pos as.length
  have hB := Nat.two_pow_pos ds.length
  let u := x.set base b |>.set count as.length |>.set modulus (2 ^ m)
    |>.set initial s.toNat |>.set heads h |>.set frontier f |>.set keyModulus (2 ^ p)
  have setup := transfer_exec b as.length (2 ^ m) s.toNat h f (2 ^ p) x
    (hfit.of_le (by have := s.isLt; omega))
  obtain ⟨z, hz, zm, _, _⟩ := prepare_exec (W := W) (b := b) (h := h) (f := f) (p := p)
    as s u
    (by simp +decide [u, base, count, modulus, initial, heads, frontier, keyModulus])
    (by simp +decide [u, count, modulus, initial, heads, frontier, keyModulus])
    (by simp +decide [u, modulus, initial, heads, frontier, keyModulus])
    (by simp +decide [u, initial, heads, frontier, keyModulus])
    (by simp +decide [u, heads, frontier, keyModulus])
    (by simp +decide [u, frontier, keyModulus]) (by simp [u]) hfirst
    (by intro i hi; exact ⟨by omega, by omega⟩) (hfit.of_le (by omega))
  simp only [u, Data.set_mem] at zm
  have zframe (a : ℕ) (ha : a < h ∨ h₄ ≤ a) : z.mem a = x.mem a := by
    have haH : ¬(h ≤ a ∧ a < h + 2 ^ p) := by omega
    rw [zm, preparedMemory_outside as s _ h f (2 ^ p) (2 ^ as.length) a
      (Nat.two_pow_pos p) haH (by omega), clear_of_not_owns haH]
  let v := z.set base b₄ |>.set count ds.length |>.set modulus (2 ^ m)
    |>.set initial t.toNat |>.set heads h₄ |>.set frontier f₄ |>.set keyModulus (2 ^ p)
  have setup₄ := transfer_exec b₄ ds.length (2 ^ m) t.toNat h₄ f₄ (2 ^ p) z
    (hfit.of_le (by have := t.isLt; omega))
  obtain ⟨y, hy, ym, _, _⟩ := Backward.prepare_exec
    (W := W) (b := b₄) (h := h₄) (f := f₄) (p := p) ds t v
    (by simp +decide [v, base, count, modulus, initial, heads, frontier, keyModulus])
    (by simp +decide [v, count, modulus, initial, heads, frontier, keyModulus])
    (by simp +decide [v, modulus, initial, heads, frontier, keyModulus])
    (by simp +decide [v, initial, heads, frontier, keyModulus])
    (by simp +decide [v, heads, frontier, keyModulus])
    (by simp +decide [v, frontier, keyModulus]) (by simp [v])
    (by intro i hi; change z.mem _ = _
        rw [zframe _ (Or.inl (by omega))]; exact hfourth i (by simpa using hi))
    (by intro i hi; exact ⟨by omega, by omega⟩) (hfit.of_le (by omega))
  simp only [v, Data.set_mem] at ym
  have yframe (a : ℕ) (ha : a < h₄ ∨ D ≤ a) : y.mem a = z.mem a := by
    have haH : ¬(h₄ ≤ a ∧ a < h₄ + 2 ^ p) := by omega
    rw [ym, Backward.preparedMemory_outside ds t _ h₄ f₄ (2 ^ p) (2 ^ ds.length) a
      (Nat.two_pow_pos p) haH (by omega), clear_of_not_owns haH]
  refine ⟨y, ?_, ?_, ?_, ?_, ?_⟩
  · exact (setup.seq (hz.seq (setup₄.seq hy))).mono (by omega)
  · simpa only [pairMemory, zm] using ym
  · intro k
    rw [yframe _ (Or.inl (by have := k.isLt; omega)), zm]
    exact (preparedMemory_linked as s _ h f (2 ^ p) (2 ^ as.length) k.toNat k.isLt
      hfpos hheads (clear_of_owns ⟨Nat.le_add_right _ _, Nat.add_lt_add_left k.isLt _⟩)).frame
      (mem' := y.mem)
      (fun a ha => by rw [← zm]; exact yframe a (Or.inl (by omega)))
  · intro k
    rw [ym]
    simpa only [inverseRecords] using
      Backward.preparedMemory_linked ds t (clear z.mem h₄ (2 ^ p)) h₄ f₄ (2 ^ p) (2 ^ ds.length)
      k.toNat k.isLt (by omega) hheads₄
      (clear_of_owns ⟨Nat.le_add_right _ _, Nat.add_lt_add_left k.isLt _⟩)
  · intro a ha
    rw [yframe a (by omega), zframe a (by omega)]

end Cslib.Cryptanalysis.AddXNOR.Native.Quarter
